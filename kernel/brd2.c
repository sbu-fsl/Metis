/*
 * Ram backed block device driver.
 *
 * Copyright (C) 2007 Nick Piggin
 * Copyright (C) 2007 Novell Inc.
 *
 * Parts derived from drivers/block/rd.c, and drivers/block/loop.c, copyright
 * of their respective owners.
 */

#include <linux/init.h>
#include <linux/initrd.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/major.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/highmem.h>
#include <linux/mutex.h>
#include <linux/radix-tree.h>
#include <linux/fs.h>
#include <linux/slab.h>
#include <linux/backing-dev.h>

#include <linux/uaccess.h>

#define SECTOR_SHIFT		9
#define PAGE_SECTORS_SHIFT	(PAGE_SHIFT - SECTOR_SHIFT)
#define PAGE_SECTORS		(1 << PAGE_SECTORS_SHIFT)
#define MAX_RD_SIZES		16

/*
 * Each block ramdisk device has a radix_tree brd2_pages of pages that stores
 * the pages containing the block device's contents. A brd2 page's ->index is
 * its offset in PAGE_SIZE units. This is similar to, but in no way connected
 * with, the kernel's pagecache or buffer cache (which sit above our block
 * device).
 */
struct brd2_device {
	int		brd2_number;

	struct request_queue	*brd2_queue;
	struct gendisk		*brd2_disk;
	struct list_head	brd2_list;

	/*
	 * Backing store of pages and lock to protect it. This is the contents
	 * of the block device.
	 */
	spinlock_t		brd2_lock;
	struct radix_tree_root	brd2_pages;
};

/*
 * Look up and return a brd2's page for a given sector.
 */
static struct page *brd2_lookup_page(struct brd2_device *brd2, sector_t sector)
{
	pgoff_t idx;
	struct page *page;

	/*
	 * The page lifetime is protected by the fact that we have opened the
	 * device node -- brd2 pages will never be deleted under us, so we
	 * don't need any further locking or refcounting.
	 *
	 * This is strictly true for the radix-tree nodes as well (ie. we
	 * don't actually need the rcu_read_lock()), however that is not a
	 * documented feature of the radix-tree API so it is better to be
	 * safe here (we don't have total exclusion from radix tree updates
	 * here, only deletes).
	 */
	rcu_read_lock();
	idx = sector >> PAGE_SECTORS_SHIFT; /* sector to page index */
	page = radix_tree_lookup(&brd2->brd2_pages, idx);
	rcu_read_unlock();

	BUG_ON(page && page->index != idx);

	return page;
}

/*
 * Look up and return a brd2's page for a given sector.
 * If one does not exist, allocate an empty page, and insert that. Then
 * return it.
 */
static struct page *brd2_insert_page(struct brd2_device *brd2, sector_t sector)
{
	pgoff_t idx;
	struct page *page;
	gfp_t gfp_flags;

	page = brd2_lookup_page(brd2, sector);
	if (page)
		return page;

	/*
	 * Must use NOIO because we don't want to recurse back into the
	 * block or filesystem layers from page reclaim.
	 *
	 * Cannot support DAX and highmem, because our ->direct_access
	 * routine for DAX must return memory that is always addressable.
	 * If DAX was reworked to use pfns and kmap throughout, this
	 * restriction might be able to be lifted.
	 */
	gfp_flags = GFP_NOIO | __GFP_ZERO;
	page = alloc_page(gfp_flags);
	if (!page)
		return NULL;

	if (radix_tree_preload(GFP_NOIO)) {
		__free_page(page);
		return NULL;
	}

	spin_lock(&brd2->brd2_lock);
	idx = sector >> PAGE_SECTORS_SHIFT;
	page->index = idx;
	if (radix_tree_insert(&brd2->brd2_pages, idx, page)) {
		__free_page(page);
		page = radix_tree_lookup(&brd2->brd2_pages, idx);
		BUG_ON(!page);
		BUG_ON(page->index != idx);
	}
	spin_unlock(&brd2->brd2_lock);

	radix_tree_preload_end();

	return page;
}

/*
 * Free all backing store pages and radix tree. This must only be called when
 * there are no other users of the device.
 */
#define FREE_BATCH 16
static void brd2_free_pages(struct brd2_device *brd2)
{
	unsigned long pos = 0;
	struct page *pages[FREE_BATCH];
	int nr_pages;

	do {
		int i;

		nr_pages = radix_tree_gang_lookup(&brd2->brd2_pages,
				(void **)pages, pos, FREE_BATCH);

		for (i = 0; i < nr_pages; i++) {
			void *ret;

			BUG_ON(pages[i]->index < pos);
			pos = pages[i]->index;
			ret = radix_tree_delete(&brd2->brd2_pages, pos);
			BUG_ON(!ret || ret != pages[i]);
			__free_page(pages[i]);
		}

		pos++;

		/*
		 * This assumes radix_tree_gang_lookup always returns as
		 * many pages as possible. If the radix-tree code changes,
		 * so will this have to.
		 */
	} while (nr_pages == FREE_BATCH);
}

/*
 * copy_to_brd2_setup must be called before copy_to_brd2. It may sleep.
 */
static int copy_to_brd2_setup(struct brd2_device *brd2, sector_t sector, size_t n)
{
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	if (!brd2_insert_page(brd2, sector))
		return -ENOSPC;
	if (copy < n) {
		sector += copy >> SECTOR_SHIFT;
		if (!brd2_insert_page(brd2, sector))
			return -ENOSPC;
	}
	return 0;
}

/*
 * Copy n bytes from src to the brd2 starting at sector. Does not sleep.
 */
static void copy_to_brd2(struct brd2_device *brd2, const void *src,
			sector_t sector, size_t n)
{
	struct page *page;
	void *dst;
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	page = brd2_lookup_page(brd2, sector);
	BUG_ON(!page);

	dst = kmap_atomic(page);
	memcpy(dst + offset, src, copy);
	kunmap_atomic(dst);

	if (copy < n) {
		src += copy;
		sector += copy >> SECTOR_SHIFT;
		copy = n - copy;
		page = brd2_lookup_page(brd2, sector);
		BUG_ON(!page);

		dst = kmap_atomic(page);
		memcpy(dst, src, copy);
		kunmap_atomic(dst);
	}
}

/*
 * Copy n bytes to dst from the brd2 starting at sector. Does not sleep.
 */
static void copy_from_brd2(void *dst, struct brd2_device *brd2,
			sector_t sector, size_t n)
{
	struct page *page;
	void *src;
	unsigned int offset = (sector & (PAGE_SECTORS-1)) << SECTOR_SHIFT;
	size_t copy;

	copy = min_t(size_t, n, PAGE_SIZE - offset);
	page = brd2_lookup_page(brd2, sector);
	if (page) {
		src = kmap_atomic(page);
		memcpy(dst, src + offset, copy);
		kunmap_atomic(src);
	} else
		memset(dst, 0, copy);

	if (copy < n) {
		dst += copy;
		sector += copy >> SECTOR_SHIFT;
		copy = n - copy;
		page = brd2_lookup_page(brd2, sector);
		if (page) {
			src = kmap_atomic(page);
			memcpy(dst, src, copy);
			kunmap_atomic(src);
		} else
			memset(dst, 0, copy);
	}
}

/*
 * Process a single bvec of a bio.
 */
static int brd2_do_bvec(struct brd2_device *brd2, struct page *page,
			unsigned int len, unsigned int off, bool is_write,
			sector_t sector)
{
	void *mem;
	int err = 0;

	if (is_write) {
		err = copy_to_brd2_setup(brd2, sector, len);
		if (err)
			goto out;
	}

	mem = kmap_atomic(page);
	if (!is_write) {
		copy_from_brd2(mem + off, brd2, sector, len);
		flush_dcache_page(page);
	} else {
		flush_dcache_page(page);
		copy_to_brd2(brd2, mem + off, sector, len);
	}
	kunmap_atomic(mem);

out:
	return err;
}

static blk_qc_t brd2_make_request(struct request_queue *q, struct bio *bio)
{
	struct brd2_device *brd2 = bio->bi_disk->private_data;
	struct bio_vec bvec;
	sector_t sector;
	struct bvec_iter iter;

	sector = bio->bi_iter.bi_sector;
	if (bio_end_sector(bio) > get_capacity(bio->bi_disk))
		goto io_error;

	bio_for_each_segment(bvec, bio, iter) {
		unsigned int len = bvec.bv_len;
		int err;

		err = brd2_do_bvec(brd2, bvec.bv_page, len, bvec.bv_offset,
					op_is_write(bio_op(bio)), sector);
		if (err)
			goto io_error;
		sector += len >> SECTOR_SHIFT;
	}

	bio_endio(bio);
	return BLK_QC_T_NONE;
io_error:
	bio_io_error(bio);
	return BLK_QC_T_NONE;
}

static int brd2_rw_page(struct block_device *bdev, sector_t sector,
		       struct page *page, bool is_write)
{
	struct brd2_device *brd2 = bdev->bd_disk->private_data;
	int err;

	if (PageTransHuge(page))
		return -ENOTSUPP;
	err = brd2_do_bvec(brd2, page, PAGE_SIZE, 0, is_write, sector);
	page_endio(page, is_write, err);
	return err;
}

static const struct block_device_operations brd2_fops = {
	.owner =		THIS_MODULE,
	.rw_page =		brd2_rw_page,
};

/*
 * And now the modules code and kernel interface.
 * For example:
 * $ sudo modprobe brd2 rd_nr=4 rd_sizes=128,256,512,1024
 * - rd_sizes is a list of sizes of each RAM block device in KB.
 * - If this parameter is not specified, all ramdisks will have the
 * size of CONFIG_BLK_DEV_RAM_SIZE (by default 4096) kilobytes.
 * - If there are fewer rd_sizes numbers than rd_nr, the rest of
 * ramdisks will have the size of the last rd_sizes number.
 */
static int rd_nr = CONFIG_BLK_DEV_RAM_COUNT;
module_param(rd_nr, int, S_IRUGO);
MODULE_PARM_DESC(rd_nr, "Maximum number of brd2 devices");

unsigned long rd_size = CONFIG_BLK_DEV_RAM_SIZE;
static unsigned long rd_sizes[MAX_RD_SIZES];
static int n_rd_sizes;
module_param_array(rd_sizes, ulong, &n_rd_sizes, S_IRUGO);
MODULE_PARM_DESC(rd_sizes, "Sizes of each RAM disk in kbytes, separated by comma.");

static int max_part = 1;
module_param(max_part, int, S_IRUGO);
MODULE_PARM_DESC(max_part, "Num Minors to reserve between devices");

MODULE_LICENSE("GPL");
MODULE_ALIAS_BLOCKDEV_MAJOR(RAMDISK_MAJOR);
MODULE_ALIAS("rd");

#ifndef MODULE
/* Legacy boot options - nonmodular */
static int __init ramdisk_size(char *str)
{
	rd_size = simple_strtol(str, NULL, 0);
	return 1;
}
__setup("ramdisk_size=", ramdisk_size);
#endif

/*
 * The device scheme is derived from loop.c. Keep them in synch where possible
 * (should share code eventually).
 */
static LIST_HEAD(brd2_devices);
static DEFINE_MUTEX(brd2_devices_mutex);

static unsigned long get_ith_ramdisk_size(int i)
{
	if (n_rd_sizes <= 0)
		return rd_size;
	if (i >= n_rd_sizes)
		return rd_sizes[n_rd_sizes - 1];
	
	return rd_sizes[i];
}

static struct brd2_device *brd2_alloc(int i)
{
	struct brd2_device *brd2;
	struct gendisk *disk;

	brd2 = kzalloc(sizeof(*brd2), GFP_KERNEL);
	if (!brd2)
		goto out;
	brd2->brd2_number		= i;
	spin_lock_init(&brd2->brd2_lock);
	INIT_RADIX_TREE(&brd2->brd2_pages, GFP_ATOMIC);

	brd2->brd2_queue = blk_alloc_queue(GFP_KERNEL);
	if (!brd2->brd2_queue)
		goto out_free_dev;

	blk_queue_make_request(brd2->brd2_queue, brd2_make_request);
	blk_queue_max_hw_sectors(brd2->brd2_queue, 1024);

	/* This is so fdisk will align partitions on 4k, because of
	 * direct_access API needing 4k alignment, returning a PFN
	 * (This is only a problem on very small devices <= 4M,
	 *  otherwise fdisk will align on 1M. Regardless this call
	 *  is harmless)
	 */
	blk_queue_physical_block_size(brd2->brd2_queue, PAGE_SIZE);
	disk = brd2->brd2_disk = alloc_disk(max_part);
	if (!disk)
		goto out_free_queue;
	disk->major		= RAMDISK_MAJOR;
	disk->first_minor	= i * max_part;
	disk->fops		= &brd2_fops;
	disk->private_data	= brd2;
	disk->queue		= brd2->brd2_queue;
	disk->flags		= GENHD_FL_EXT_DEVT;
	sprintf(disk->disk_name, "ram%d", i);
	set_capacity(disk, get_ith_ramdisk_size(i) * 2);
	disk->queue->backing_dev_info->capabilities |= BDI_CAP_SYNCHRONOUS_IO;

	return brd2;

out_free_queue:
	blk_cleanup_queue(brd2->brd2_queue);
out_free_dev:
	kfree(brd2);
out:
	return NULL;
}

static void brd2_free(struct brd2_device *brd2)
{
	put_disk(brd2->brd2_disk);
	blk_cleanup_queue(brd2->brd2_queue);
	brd2_free_pages(brd2);
	kfree(brd2);
}

static struct brd2_device *brd2_init_one(int i, bool *new)
{
	struct brd2_device *brd2;

	*new = false;
	list_for_each_entry(brd2, &brd2_devices, brd2_list) {
		if (brd2->brd2_number == i)
			goto out;
	}

	brd2 = brd2_alloc(i);
	if (brd2) {
		add_disk(brd2->brd2_disk);
		list_add_tail(&brd2->brd2_list, &brd2_devices);
	}
	*new = true;
out:
	return brd2;
}

static void brd2_del_one(struct brd2_device *brd2)
{
	list_del(&brd2->brd2_list);
	del_gendisk(brd2->brd2_disk);
	brd2_free(brd2);
}

static struct kobject *brd2_probe(dev_t dev, int *part, void *data)
{
	struct brd2_device *brd2;
	struct kobject *kobj;
	bool new;

	mutex_lock(&brd2_devices_mutex);
	brd2 = brd2_init_one(MINOR(dev) / max_part, &new);
	kobj = brd2 ? get_disk(brd2->brd2_disk) : NULL;
	mutex_unlock(&brd2_devices_mutex);

	if (new)
		*part = 0;

	return kobj;
}

static int __init brd2_init(void)
{
	struct brd2_device *brd2, *next;
	int i;

	/*
	 * brd2 module now has a feature to instantiate underlying device
	 * structure on-demand, provided that there is an access dev node.
	 *
	 * (1) if rd_nr is specified, create that many upfront. else
	 *     it defaults to CONFIG_BLK_DEV_RAM_COUNT
	 * (2) User can further extend brd2 devices by create dev node themselves
	 *     and have kernel automatically instantiate actual device
	 *     on-demand. Example:
	 *		mknod /path/devnod_name b 1 X	# 1 is the rd major
	 *		fdisk -l /path/devnod_name
	 *	If (X / max_part) was not already created it will be created
	 *	dynamically.
	 */

	if (register_blkdev(RAMDISK_MAJOR, "ramdisks"))
		return -EIO;

	if (unlikely(!max_part))
		max_part = 1;

	for (i = 0; i < rd_nr; i++) {
		brd2 = brd2_alloc(i);
		if (!brd2)
			goto out_free;
		list_add_tail(&brd2->brd2_list, &brd2_devices);
	}

	/* point of no return */

	list_for_each_entry(brd2, &brd2_devices, brd2_list)
		add_disk(brd2->brd2_disk);

	blk_register_region(MKDEV(RAMDISK_MAJOR, 0), 1UL << MINORBITS,
				  THIS_MODULE, brd2_probe, NULL, NULL);

	pr_info("brd2: module loaded\n");
	return 0;

out_free:
	list_for_each_entry_safe(brd2, next, &brd2_devices, brd2_list) {
		list_del(&brd2->brd2_list);
		brd2_free(brd2);
	}
	unregister_blkdev(RAMDISK_MAJOR, "ramdisks");

	pr_info("brd2: module NOT loaded !!!\n");
	return -ENOMEM;
}

static void __exit brd2_exit(void)
{
	struct brd2_device *brd2, *next;

	list_for_each_entry_safe(brd2, next, &brd2_devices, brd2_list)
		brd2_del_one(brd2);

	blk_unregister_region(MKDEV(RAMDISK_MAJOR, 0), 1UL << MINORBITS);
	unregister_blkdev(RAMDISK_MAJOR, "ramdisks");

	pr_info("brd2: module unloaded\n");
}

module_init(brd2_init);
module_exit(brd2_exit);

