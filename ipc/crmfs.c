#include "crmfs.h"

static size_t icap;
static size_t dcap;
static struct fuse_chan *crmfs_ch;
static struct fuse_session *crmfs_se;
static const unsigned long crmfs_magic = 0xf09f90b120e596b5;
struct crmfs_file *files;
pthread_mutex_t global_lk;

static void crmfs_lock(const char *caller)
{
    printf("%s: lock\n", caller);
    pthread_mutex_lock(&global_lk);
}

static void crmfs_unlock(const char *caller)
{
    printf("%s: unlock\n", caller);
    pthread_mutex_unlock(&global_lk);
}

static struct crmfs_file *crmfs_file_create(mode_t filetype, mode_t perm, uid_t uid, gid_t gid)
{
    struct crmfs_file *newf = NULL;
    int i;
    enter();
    for (i = 0; i < icap; ++i) {
        if ((files[i].flag & CRM_FILE_EXIST) == 0) {
            newf = files + i;
            break;
        }
    }
    if (!newf) {
        debug("%s: no file slot.\n", __func__);
        return NULL;
    }
    memset(newf, 0, sizeof(struct crmfs_file));
    newf->flag |= CRM_FILE_EXIST;
    CRM_FILE_ATTR(newf, mode) = (filetype | perm);
    CRM_FILE_ATTR(newf, ino) = i + 1;
    CRM_FILE_ATTR(newf, nlink) = 1;
    CRM_FILE_ATTR(newf, uid) = uid;
    CRM_FILE_ATTR(newf, gid) = gid;
    CRM_FILE_ATTR(newf, blksize) = CRM_BLOCK_SZ;
    newf->entry_param.ino = i + 1;
    newf->entry_param.attr_timeout = 1.0;
    newf->entry_param.entry_timeout = 1.0;
    return newf;
}

static void crmfs_destroy_file(struct crmfs_file *f)
{
    enter();
    if (!f)
        return;
    if (f->data)
        free(f->data);
    memset(f, 0, sizeof(struct crmfs_file));
}

static int crmfs_sanitize_file(struct crmfs_file *f, mode_t expect_file_type,
        bool expect_empty)
{
    enter();
    if (!f) {
        debug("input file pointer is null\n");
        return -EFAULT;
    }
    if (!(f->flag & CRM_FILE_EXIST)) {
        debug("file is an unused slot\n");
        return -ENOENT;
    }
    if (CRM_FILE_ATTR(f, nlink) == 0) {
        debug("file has no link\n");
        return -ENOENT;
    }
    /* Check file type */
    if (expect_file_type & __S_IFREG) {
        if (!S_ISREG(CRM_FILE_ATTR(f, mode))) {
            debug("expected regular file\n");
            return -EISDIR;
        }
    } else if (expect_file_type & __S_IFDIR) {
        if (!S_ISDIR(CRM_FILE_ATTR(f, mode))) {
            debug("expected dir\n");
            return -ENOTDIR;
        }
    }
    /* Check emptiness */
    if (CRM_FILE_ATTR(f, blocks) > 0 && f->data == NULL) {
        debug("st_blocks > 0 but data is null\n");
        return -EINVAL;
    }
    if (expect_empty) {
        if (CRM_FILE_ATTR(f, blocks) > 0) {
            debug("expected empty but is not\n");
            return -ENOTEMPTY;
        }
    } else {
        if (CRM_FILE_ATTR(f, blocks) == 0) {
            debug("expected not empty but is empty\n");
            return -ENODATA;
        }
    }
    return 0;
}

static int crmfs_more_blocks(struct crmfs_file *f, ssize_t incr)
{
    size_t old_n = CRM_FILE_ATTR(f, blocks);
    size_t oldsize = old_n * CRM_BLOCK_SZ;
    size_t newsize = (old_n + incr) * CRM_BLOCK_SZ;
    void *data;
    enter();
    if (!(f->flag & CRM_FILE_EXIST)) {
        debug("file is an unused slot\n");
        return -EINVAL;
    }

    data = realloc(f->data, newsize);
    if (newsize > 0 && !data) {
        debug("failed to realloc\n");
        return -ENOSPC;
    }
    /* Zero out new memory area */
    if (newsize > oldsize) {
        char *p = data + oldsize;
        memset(p, 0, newsize - oldsize);
    }
    f->data = data;
    CRM_FILE_ATTR(f, blocks) = old_n + incr;
    return 0;
}

static int crmfs_file_truncate(struct crmfs_file *file, size_t newsize)
{
    enter();
    int ret = crmfs_sanitize_file(file, __S_IFREG, false);
    if (ret && ret != -ENODATA)
        return ret;

    size_t oldsize = CRM_FILE_ATTR(file, size);
    size_t oldblock = CRM_FILE_ATTR(file, blocks);
    ssize_t newblock = (newsize > 0) ? nblocks(newsize) : 0;
    
    /* Adjust number of blocks for this file - might expand or shrink
     * depending on newblock - oldblock */
    if (oldblock != newblock) {
        ret = crmfs_more_blocks(file, newblock - oldblock);
    } else {
        ret = 0;
    }
    /* Zero out new space inside the old last block if the file is
     * expanded */
    if (newsize > oldsize && (oldsize & (CRM_BLOCK_SZ - 1)) > 0) {
        char *p = (char *)file->data + oldsize;
        size_t bytes_need_clean = round_up(oldsize, CRM_BLOCK_SZ) - oldsize;
        memset(p, 0, bytes_need_clean);
    }
    CRM_FILE_ATTR(file, size) = newsize;
    return ret;
}

static int crmfs_populate_dir(struct crmfs_file *dir, struct crmfs_file *parent)
{
    const size_t nblocks = 8;
    enter();
    int ret = crmfs_sanitize_file(dir, __S_IFDIR, true);
    if (ret)
        return ret;

    ret = crmfs_more_blocks(dir, nblocks);
    if (ret)
        return ret;

    struct crmfs_dirtable *table = dir->data;
    size_t cap = (nblocks * CRM_BLOCK_SZ - sizeof(struct crmfs_dirtable)) /
        sizeof(struct crmfs_dirent);
    table->capacity = cap;
    /* '.' and '..' */
    table->ndirs = 2;
    table->dirents[0].ino = CRM_FILE_ATTR(dir, ino);
    table->dirents[1].ino = CRM_FILE_ATTR(parent, ino);
    strcpy(table->dirents[0].name, ".");
    strcpy(table->dirents[1].name, "..");
    CRM_FILE_ATTR(dir, nlink) = 2;
    return 0;
}

static int crmfs_dir_add_child(struct crmfs_file *dir, struct crmfs_file *child,
                               const char *name)
{
    enter();
    const size_t n_more_blocks = 8;
    int ret = crmfs_sanitize_file(dir, __S_IFDIR, false);
    struct crmfs_dirtable *table = dir->data;
    struct crmfs_dirent *dirent = NULL;
    size_t i;
    if (ret)
        return ret;
    /* Can we find an existing slot within the capacity? */
    for (i = 0; i < table->capacity; ++i) {
        if (table->dirents[i].ino == 0) {
            dirent = table->dirents + i;
            break;
        }
    }
    /* If not, we need to expand the dir table */
    if (!dirent) {
        ret = crmfs_more_blocks(dir, n_more_blocks);
        if (ret)
            return ret;
        size_t new_size = CRM_BLOCK_SZ * CRM_FILE_ATTR(dir, blocks);
        size_t new_cap = (new_size - sizeof(struct crmfs_dirtable)) / sizeof(struct crmfs_dirent);
        table->capacity = new_cap;
        /* i should be equal to the old entry capacity */
        dirent = table->dirents + i;
    }
    strncpy(dirent->name, name, NAME_MAX);
    dirent->ino = CRM_FILE_ATTR(child, ino);
    table->ndirs++;
    return 0;
}

static int crmfs_dir_remove_child(struct crmfs_file *dir, const char *name)
{
    enter();
    int ret = crmfs_sanitize_file(dir, __S_IFDIR, false);
    struct crmfs_dirtable *table = dir->data;
    struct crmfs_dirent *dirent = NULL;
    if (ret)
        return ret;
    for (int i = 0; i < table->capacity; ++i) {
        if (strncmp(name, table->dirents[i].name, NAME_MAX) == 0) {
            dirent = table->dirents + i;
            break;
        }
    }
    if (!dirent) {
        debug("child %s does not exist\n", name);
        return -ENOENT;
    }
    dirent->ino = 0;
    dirent->name[0] = '\0';
    table->ndirs--;
    return 0;
}

static struct crmfs_file *crmfs_find_child(struct crmfs_file *dir, const char *name)
{
    enter();
    int ret = crmfs_sanitize_file(dir, __S_IFDIR, false);
    struct crmfs_dirtable *table = dir->data;
    struct crmfs_dirent *dirent = NULL;
    if (ret)
        return ERR_PTR(ret);
    for (int i = 0; i < table->capacity; ++i) {
        if (strncmp(name, table->dirents[i].name, NAME_MAX) == 0) {
            dirent = table->dirents + i;
            break;
        }
    }
    if (!dirent || dirent->ino == 0 || dirent->ino >= icap) {
        debug("cannot find child %s: dirent=%p, ino=%ld\n", dirent,
              dirent ? dirent->ino : 0);
        return ERR_PTR(-ENOENT);
    }
    return files + dirent->ino - 1;
}

static struct crmfs_file *crmfs_iget(fuse_ino_t ino)
{
    enter();
    if (ino <= 0 || ino >= icap) {
        debug("invalid inode number %ld\n", ino);
        return NULL;
    }
    struct crmfs_file *file = &files[ino - 1];
    if (!(file->flag & CRM_FILE_EXIST)) {
        debug("inode %ld is an unused slot\n", ino);
        return NULL;
    }
    if (CRM_FILE_ATTR(file, nlink) <= 0) {
        debug("inode %ld has no links\n", ino);
        return NULL;
    }
    return file;
}

static void crmfs_init(void *userdata, struct fuse_conn_info *conn)
{
    enter();
    icap = CRM_DEFAULT_ICAP;
    dcap = 0;
    files = calloc(icap, sizeof(struct crmfs_file));
    /* Create the first inode (root directory) */
    struct crmfs_file *root = crmfs_file_create(__S_IFDIR, 0755, getuid(), getgid());
    assert(root != NULL);
    int ret = crmfs_populate_dir(root, root);
    assert(ret == 0);
    /* Enable ioctl on directory */
    conn->want |= FUSE_CAP_IOCTL_DIR;
}

static void crmfs_destroy(void *userdata)
{
    enter();
    for (size_t i = 0; i < icap; ++i) {
        struct crmfs_file *f = files + i;
        if (f->flag & CRM_FILE_EXIST) {
            free(f->data);
        }
    }
    free(files);
    files = NULL;
}

static void crmfs_lookup(fuse_req_t req, fuse_ino_t parent_ino, const char *name)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *parent = crmfs_iget(parent_ino);
    if (!parent) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    struct crmfs_file *child = crmfs_find_child(parent, name);
    if (IS_ERR(child)) {
        fuse_reply_err(req, -PTR_ERR(child));
        goto end;
    }
    child->nlookup++;
    fuse_reply_entry(req, &child->entry_param);
end:
    crmfs_unlock(__func__);
}

static void crmfs_getattr(fuse_req_t req, fuse_ino_t ino,
                          struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    fuse_reply_attr(req, &file->entry_param.attr, 1.0);
end:
    crmfs_unlock(__func__);
}

static void do_setattr(struct crmfs_file *file, struct stat *attr, int to_set)
{
    enter();
    if (to_set & FUSE_SET_ATTR_MODE) {
        CRM_FILE_ATTR(file, mode) = attr->st_mode;
    }
    if (to_set & FUSE_SET_ATTR_UID) {
        CRM_FILE_ATTR(file, uid) = attr->st_uid;
    }
    if (to_set & FUSE_SET_ATTR_GID) {
        CRM_FILE_ATTR(file, gid) = attr->st_gid;
    }
    if (to_set & FUSE_SET_ATTR_SIZE) {
        CRM_FILE_ATTR(file, size) = attr->st_size;
    }
    if (to_set & FUSE_SET_ATTR_ATIME) {
#ifdef __APPLE__
        CRM_FILE_ATTR(file, atimespec) = attr->st_atimespec;
#else
        CRM_FILE_ATTR(file, atim) = attr->st_atim;
#endif
    }
    if (to_set & FUSE_SET_ATTR_MTIME) {
#ifdef __APPLE__
        CRM_FILE_ATTR(file, mtimespec) = attr->st_mtimespec;
#else
        CRM_FILE_ATTR(file, mtim) = attr->st_mtim;
#endif
    }
#ifdef __APPLE__
    if (to_set & FUSE_SET_ATTR_CRTIME) {
        CRM_FILE_ATTR(file, birthtimespec) = attr->st_birthtimespec;
    }
    // TODO: Can't seem to find this one.
//    if (to_set & FUSE_SET_ATTR_BKUPTIME) {
//        CRM_FILE_ATTR(file,  = attr->st_mode;
//    }
    if (to_set & FUSE_SET_ATTR_FLAGS) {
        CRM_FILE_ATTR(file, flags = attr->st_flags;
    }
#endif /* __APPLE__ */
    
    // TODO: What do we do if this fails? Do we care? Log the event?
#ifdef __APPLE__
    clock_gettime(CLOCK_REALTIME, &CRM_FILE_ATTR(file, ctimespec));
#else
    clock_gettime(CLOCK_REALTIME, &CRM_FILE_ATTR(file, ctim));
#endif

}

static void crmfs_setattr(fuse_req_t req, fuse_ino_t ino, struct stat *attr,
                          int to_set, struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    int ret;

    /* Truncate file if FUSE_SET_ATTR_SIZE is called */
    if (to_set & FUSE_SET_ATTR_SIZE) {
        ret = crmfs_file_truncate(file, attr->st_size);
        if (ret == 0) {
            fuse_reply_attr(req, &file->entry_param.attr, 1.0);
        } else {
            fuse_reply_err(req, -ret);
        }
        goto end;
    }

    do_setattr(file, attr, to_set);
    fuse_reply_attr(req, &file->entry_param.attr, 1.0);
end:
    crmfs_unlock(__func__);
}

static void crmfs_fsync_dir(fuse_req_t req, fuse_ino_t ino, int datasync,
                            struct fuse_file_info *fi)
{
    enter();
    fuse_reply_err(req, 0);
}

static void crmfs_read_dir(fuse_req_t req, fuse_ino_t ino, size_t size,
                           off_t off, struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *dir = crmfs_iget(ino);
    if (!dir) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    int ret = crmfs_sanitize_file(dir, __S_IFDIR, false);
    if (ret != 0) {
        fuse_reply_err(req, -ret);
        goto end;
    }
    
    struct crmfs_dirtable *table = dir->data;
    struct crmfs_dirent *dirents = table->dirents;

    /* If the given offset is out of range, return an empty buffer */
    if (off < 0 || off >= table->capacity) {
        fuse_reply_buf(req, NULL, 0);
        goto end;
    }
    char *buffer = malloc(size);
    size_t bytes_added = 0;
    off_t i;
    if (buffer == NULL) {
        fuse_reply_err(req, ENOMEM);
        goto end;
    }

    /* Fill the buffer with dir entries */
    for (i = off; i < table->capacity; ++i) {
        struct crmfs_file *child = NULL;
        if (dirents[i].ino > 0)
            child = crmfs_iget(dirents[i].ino);
        if (!child)
            continue;
        struct stat *attrs = &child->entry_param.attr;
        size_t bytes_incr = fuse_add_direntry(req, buffer + bytes_added,
                size - bytes_added, dirents[i].name, attrs, i + 1);
        /* If the buffer does not have enough space to hold this entry,
         * fuse_add_direnty will not actually add the entry and we should
         * jump out */
        if (bytes_added + bytes_incr > size) {
            break;
        }
        bytes_added += bytes_incr;
    }

    fuse_reply_buf(req, buffer, bytes_added);
    free(buffer);
end:
    crmfs_unlock(__func__);
}

static void crmfs_open(fuse_req_t req, fuse_ino_t ino,
                       struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    if (!S_ISREG(CRM_FILE_ATTR(file, mode))) {
        fuse_reply_err(req, EISDIR);
        goto end;
    }
    fuse_reply_open(req, fi);
end:
    crmfs_unlock(__func__);
}

static void crmfs_fsync(fuse_req_t req, fuse_ino_t ino, int datasync,
                        struct fuse_file_info *fi)
{
    enter();
    fuse_reply_err(req, 0);
}

static void crmfs_mknod(fuse_req_t req, fuse_ino_t parent, const char *name,
                        mode_t mode, dev_t rdev)
{
    enter();
    fuse_reply_err(req, ENOTSUP);
}

static void crmfs_mkdir(fuse_req_t req, fuse_ino_t parent_ino, const char *name,
                        mode_t mode)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *parent = crmfs_iget(parent_ino);
    struct crmfs_file *child = crmfs_find_child(parent, name);
    if (!IS_ERR(child)) {
        debug("child %s has already existed\n", name);
        fuse_reply_err(req, EEXIST);
        goto end;
    } else if (IS_ERR(child) && PTR_ERR(child) != -ENOENT) {
        fuse_reply_err(req, -PTR_ERR(child));
        goto end;
    }

    child = crmfs_file_create(__S_IFDIR, mode, getuid(), getgid());
    if (!child) {
        fuse_reply_err(req, ENOSPC);
        goto end;
    }
    int ret = crmfs_populate_dir(child, parent);
    if (ret) {
        crmfs_destroy_file(child);
        fuse_reply_err(req, -ret);
        goto end;
    }
    ret = crmfs_dir_add_child(parent, child, name);
    if (ret) {
        crmfs_destroy_file(child);
        fuse_reply_err(req, -ret);
    }
    else {
        CRM_FILE_ATTR(parent, nlink)++;
        child->nlookup++;
        fuse_reply_entry(req, &child->entry_param);
    }
end:
    crmfs_unlock(__func__);
}

static void crmfs_create(fuse_req_t req, fuse_ino_t iparent, const char *name,
                         mode_t mode, struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *parent = crmfs_iget(iparent);
    struct crmfs_file *child = crmfs_find_child(parent, name);
    if (!IS_ERR(child)) {
        debug("child %s has already existed\n", name);
        fuse_reply_err(req, EEXIST);
        goto end;
    } else if (IS_ERR(child) && PTR_ERR(child) != -ENOENT) {
        fuse_reply_err(req, -PTR_ERR(child));
        goto end;
    }

    child = crmfs_file_create(__S_IFREG, mode, getuid(), getgid());
    if (!child) {
        fuse_reply_err(req, ENOSPC);
        goto end;
    }

    int ret = crmfs_dir_add_child(parent, child, name);
    if (ret) {
        crmfs_destroy_file(child);
        fuse_reply_err(req, -ret);
    } else {
        child->nlookup++;
        fuse_reply_create(req, &child->entry_param, fi);
    }
end:
    crmfs_unlock(__func__);
}

static void crmfs_unlink(fuse_req_t req, fuse_ino_t iparent, const char *name)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *parent = crmfs_iget(iparent);
    struct crmfs_file *child = crmfs_find_child(parent, name);
    if (IS_ERR(child)) {
        fuse_reply_err(req, -PTR_ERR(child));
        goto end;
    }
    if (S_ISDIR(CRM_FILE_ATTR(child, mode))) {
        debug("cannot unlink a directory %s\n", name);
        fuse_reply_err(req, EISDIR);
        goto end;
    }
    int ret = crmfs_dir_remove_child(parent, name);
    if (ret) {
        fuse_reply_err(req, -ret);
        goto end;
    }
    CRM_FILE_ATTR(child, nlink)--;

    fuse_reply_err(req, 0);
end:
    crmfs_unlock(__func__);
}

static void crmfs_rmdir(fuse_req_t req, fuse_ino_t iparent, const char *name)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *parent = crmfs_iget(iparent);
    struct crmfs_file *child = crmfs_find_child(parent, name);
    if (IS_ERR(child)) {
        fuse_reply_err(req, -PTR_ERR(child));
        goto end;
    }
    if (!S_ISDIR(CRM_FILE_ATTR(child, mode))) {
        debug("cannot call rmdir on a non-dir file %s\n", name);
        fuse_reply_err(req, ENOTDIR);
        goto end;
    }
    struct crmfs_dirtable *table = child->data;
    /* The dir to be deleted cannot have anything other than '.' and '..' */
    if (table->ndirs > 2) {
        debug("dir %s is not empty\n", name);
        fuse_reply_err(req, ENOTEMPTY);
        goto end;
    }
    int ret = crmfs_dir_remove_child(parent, name);
    if (ret) {
        fuse_reply_err(req, -ret);
        goto end;
    }
    CRM_FILE_ATTR(child, nlink) -= 2;
    CRM_FILE_ATTR(parent, nlink)--;

    fuse_reply_err(req, 0);
end:
    crmfs_unlock(__func__);
}

static void crmfs_forget(fuse_req_t req, fuse_ino_t ino, unsigned long nlookup)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = &files[ino - 1];
    if (!(file->flag & CRM_FILE_EXIST))
        goto end;

    file->nlookup -= nlookup;
    if (CRM_FILE_ATTR(file, nlink) == 0 && file->nlookup <= 0) {
        crmfs_destroy_file(file);
    } else {
        fprintf(stderr, "%s: warning: forget called on file %lu but did not"
                " get freed. nlookup = %d, nlink = %lu\n", __func__, ino,
                file->nlookup, CRM_FILE_ATTR(file, nlink));
    }
end:
    crmfs_unlock(__func__);
}

static void crmfs_write(fuse_req_t req, fuse_ino_t ino, const char *buf,
                        size_t size, off_t off, struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    int ret;
    if (off + size > CRM_FILE_ATTR(file, size)) {
        ret = crmfs_file_truncate(file, off + size);
    } else {
        ret = crmfs_sanitize_file(file, __S_IFREG, false);
    }
    if (ret) {
        fuse_reply_err(req, -ret);
        goto end;
    }

    char *p = file->data + off;
    memcpy(p, buf, size);
    fuse_reply_write(req, size);
end:
    crmfs_unlock(__func__);
}

static void crmfs_flush(fuse_req_t req, fuse_ino_t ino,
                        struct fuse_file_info *fi)
{
    fuse_reply_err(req, 0);
}

static void crmfs_read(fuse_req_t req, fuse_ino_t ino, size_t size, off_t off,
                       struct fuse_file_info *fi)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    int ret = crmfs_sanitize_file(file, __S_IFREG, false);
    if (ret == -ENODATA) {
        fuse_reply_buf(req, NULL, 0);
        goto end;
    } else if (ret != 0) {
        fuse_reply_err(req, -ret);
        goto end;
    }

    size_t filesize = CRM_FILE_ATTR(file, size);
    size_t bytes_read;
    char *p = file->data;
    if (off >= filesize) {
        fuse_reply_buf(req, p, 0);
        goto end;
    } else if (off + size > filesize) {
        bytes_read = filesize - off;
    } else {
        bytes_read = size;
    }
    fuse_reply_buf(req, p + off, bytes_read);
end:
    crmfs_unlock(__func__);
}

static void crmfs_rename(fuse_req_t req, fuse_ino_t parent, const char *name,
                         fuse_ino_t newparent, const char *newname)
{
    fuse_reply_err(req, ENOTSUP);
}

static void crmfs_link(fuse_req_t req, fuse_ino_t ino, fuse_ino_t newparent,
                       const char *newname)
{
    fuse_reply_err(req, ENOTSUP);
}

static void crmfs_symlink(fuse_req_t req, const char *link, fuse_ino_t parent,
                          const char *name)
{
    fuse_reply_err(req, ENOTSUP);
}

static void crmfs_readlink(fuse_req_t req, fuse_ino_t ino)
{
    fuse_reply_err(req, ENOTSUP);
}

static void crmfs_access(fuse_req_t req, fuse_ino_t ino, int mask)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *file = crmfs_iget(ino);
    if (!file) {
        fuse_reply_err(req, ENOENT);
        goto end;
    }
    if (mask == F_OK) {
        fuse_reply_err(req, 0);
        goto end;
    }
    const struct fuse_ctx *ctx = fuse_req_ctx(req);
    /* Check other */
    if ((CRM_FILE_ATTR(file, mode) & mask) == mask) {
        fuse_reply_err(req, 0);
        goto end;
    }
    /* Check group */
    mask <<= 3;
    if ((CRM_FILE_ATTR(file, mode) & mask) == mask &&
            CRM_FILE_ATTR(file, gid) == ctx->gid) {
        fuse_reply_err(req, 0);
        goto end;
    }
    /* Check owner */
    mask <<= 3;
    if ((CRM_FILE_ATTR(file, mode) & mask) == mask &&
            CRM_FILE_ATTR(file, uid) == ctx->uid) {
        fuse_reply_err(req, 0);
        goto end;
    }

    fuse_reply_err(req, EACCES);
end:
    crmfs_unlock(__func__);
}

static void crmfs_statfs(fuse_req_t req, fuse_ino_t ino)
{
    struct statvfs info = {
        .f_bsize = CRM_BLOCK_SZ,
        .f_frsize = CRM_BLOCK_SZ,
        .f_blocks = 0,
        .f_bfree = 0,
        .f_bavail = 0,
        .f_files = icap,
        .f_ffree = 0,
        .f_favail = 0,
        .f_fsid = crmfs_magic,
        .f_flag = 0,
        .f_namemax = NAME_MAX
    };

    fsfilcnt_t nfiles = 0;
    for (size_t i = 0; i < icap; ++i) {
        if (files[i].flag & CRM_FILE_EXIST) {
            nfiles++;
        }
    }
    info.f_ffree = icap - nfiles;
    info.f_favail = icap - nfiles;
    fuse_reply_statfs(req, &info);
}

static void free_files(struct crmfs_file *files_)
{
    for (size_t i = 0; i < icap; ++i) {
        if (files_[i].data) {
            free(files_[i].data);
        }
    }
    free(files_);
}

static int checkpoint(uint64_t key)
{
    enter();
    crmfs_lock(__func__);
    size_t inodes_size = icap * sizeof(struct crmfs_file);
    struct crmfs_file *copied_files = malloc(inodes_size);
    int ret = 0;
    if (!copied_files) {
        ret = -ENOMEM;
        goto err;
    }
    memcpy(copied_files, files, inodes_size);
    /* Reset the pointers */
    for (size_t i = 0; i < icap; ++i) {
        copied_files[i].data = NULL;
    }
    /* Deep copy the data */
    for (size_t i = 0; i < icap; ++i) {
        size_t datasz = CRM_FILE_ATTR(&files[i], blocks) * CRM_BLOCK_SZ;
        if (datasz == 0) {
            continue;
        }
        char *fdata = malloc(datasz);
        if (!fdata) {
            ret = -ENOMEM;
            goto err;
        }
        memcpy(fdata, files[i].data, datasz);
        copied_files[i].data = fdata;
    }

    ret = insert_state(key, copied_files);
    if (ret != 0)
        goto err;

    crmfs_unlock(__func__);
    return ret;
err:
    /* Roll back deep copy if error occurred */
    free_files(copied_files);
    crmfs_unlock(__func__);
    return ret;
}

static void invalidate_kernel_states()
{
    for (size_t i = 0; i < icap; ++i) {
        /* Invalidate possible kernel inode cache */
        if (files[i].flag & CRM_FILE_EXIST) {
            fuse_lowlevel_notify_inval_inode(crmfs_ch, i + 1, 0, 0);
        }
        /* Invalidate potential d-cache */
        if (S_ISDIR(CRM_FILE_ATTR(&files[i], mode))) {
            struct crmfs_dirtable *table = files[i].data;
            struct crmfs_dirent *dirents = table->dirents;
            for (size_t j = 0; j < table->capacity; ++j) {
                if (dirents[j].ino > 0) {
                    fuse_lowlevel_notify_inval_entry(crmfs_ch, i + 1,
                        dirents[j].name,
                        strnlen(dirents[j].name, NAME_MAX));
                }
            }
        }
    }
}

static int restore(uint64_t key)
{
    enter();
    crmfs_lock(__func__);
    struct crmfs_file *stored_files = find_state(key);
    int ret = 0;
    if (!stored_files) {
        ret = -ENOENT;
        goto err;
    }

    invalidate_kernel_states();
    size_t itable_sz = icap * sizeof(struct crmfs_file);
    /* Make a full copy of the stored inode table.
     * We only perfrom the table replacement if the entire
     * deep copying process is successful. */
    struct crmfs_file *newfiles = malloc(itable_sz);
    if (!newfiles) {
        ret = -ENOMEM;
        goto err;
    }
    memcpy(newfiles, stored_files, itable_sz);
    for (size_t i = 0; i < icap; ++i) {
        newfiles[i].data = NULL;
    }
    for (size_t i = 0; i < icap; ++i) {
        size_t dsize = CRM_FILE_ATTR(&newfiles[i], blocks) * CRM_BLOCK_SZ;
        char *fdata = malloc(dsize);
        if (!fdata) {
            ret = -ENOMEM;
            goto err;
        }
        memcpy(fdata, stored_files[i].data, dsize);
        newfiles[i].data = fdata;
    }
    /* Free the current inode table and replace it with the
     * copy retrieved from above code */
    free_files(files);
    files = newfiles;
    /* Remove the state from the pool */
    free_files(stored_files);
    remove_state(key);
    crmfs_unlock(__func__);
    return 0;
err:
    free_files(newfiles);
    crmfs_unlock(__func__);
    return ret;
}

static void crmfs_ioctl(fuse_req_t req, fuse_ino_t ino, int cmd, void *arg,
                        struct fuse_file_info *fi, unsigned flags,
                        const void *in_buf, size_t in_bufsz, size_t out_bufsz)
{
    int ret;
    enter();
    switch (cmd) {
        case CRMFS_CHECKPOINT:
            ret = checkpoint((uint64_t)arg);
            break;

        case CRMFS_RESTORE:
            ret = restore((uint64_t)arg);
            break;

        default:
            ret = ENOTSUP;
            break;
    }
    if (ret == 0) {
        fuse_reply_ioctl(req, 0, NULL, 0);
    } else {
        fuse_reply_err(req, -ret);
    }
}

struct fuse_lowlevel_ops crmfs_ops = {
    .init = crmfs_init,
    .destroy = crmfs_destroy,
    .lookup = crmfs_lookup,
    .forget = crmfs_forget,
    .getattr = crmfs_getattr,
    .setattr = crmfs_setattr,
    .mkdir = crmfs_mkdir,
    .unlink = crmfs_unlink,
    .rmdir = crmfs_rmdir,
    .open = crmfs_open,
    .read = crmfs_read,
    .write = crmfs_write,
    .flush = crmfs_flush,
    .readdir = crmfs_read_dir,
    .statfs = crmfs_statfs,
    .create = crmfs_create,
    .readlink = crmfs_readlink,
    .symlink = crmfs_symlink,
    .link = crmfs_link,
    .rename = crmfs_rename,
    .mknod = crmfs_mknod,
    .fsync = crmfs_fsync,
    .fsyncdir = crmfs_fsync_dir,
    .ioctl = crmfs_ioctl,
    .access = crmfs_access
};

int main(int argc, char **argv)
{
    struct fuse_args args = FUSE_ARGS_INIT(argc, argv);
    char *mountpoint;
    int err = -1;
    int fg;

    err = fuse_parse_cmdline(&args, &mountpoint, NULL, &fg);
    if (err == -1) {
        fprintf(stderr, "Error: cannot parse cmd line.\n");
        exit(1);
    }
    if (!mountpoint) {
        fprintf(stderr, "Error: no mount point specified.\n");
        exit(1);
    }

    crmfs_ch = fuse_mount(mountpoint, &args);
    if (!crmfs_ch) {
        fprintf(stderr, "Error: fuse_mount failed.\n");
        exit(1);
    }

    crmfs_se = fuse_lowlevel_new(&args, &crmfs_ops, sizeof(crmfs_ops), NULL);
    if (!crmfs_se) {
        fprintf(stderr, "Error: fuse_lowlevel_new failed.\n");
        exit(1);
    }
    pthread_mutex_init(&global_lk, NULL);

    fuse_daemonize(fg);
    if (fuse_set_signal_handlers(crmfs_se) != -1) {
        fuse_session_add_chan(crmfs_se, crmfs_ch);
        err = fuse_session_loop(crmfs_se);
        fuse_remove_signal_handlers(crmfs_se);
        fuse_session_remove_chan(crmfs_ch);
    }
    fuse_session_destroy(crmfs_se);
    fuse_unmount(mountpoint, crmfs_ch);

    pthread_mutex_destroy(&global_lk);

    return err ? 1 : 0;
}
