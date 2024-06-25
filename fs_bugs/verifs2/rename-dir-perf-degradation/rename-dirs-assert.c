#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/stat.h>
#include <errno.h>
#include <dirent.h>
#include <string.h>

// Function to create the test directory structure
void create_test_structure(const char *base_path) {
    char src_dir[256];
    char sub_dir[256];
    char dest_base[256];
    char dest_dir[256];

    snprintf(src_dir, sizeof(src_dir), "%s/d-00", base_path);
    snprintf(sub_dir, sizeof(sub_dir), "%s/d-00/d-01", base_path);
    snprintf(dest_base, sizeof(dest_base), "%s/d-01", base_path);
    snprintf(dest_dir, sizeof(dest_dir), "%s/d-01/d-00", base_path);

    // Create source directory and subdirectory
    mkdir(src_dir, 0755);
    mkdir(sub_dir, 0755);

    // Create destination base directory
    mkdir(dest_base, 0755);

    // Create destination directory
    mkdir(dest_dir, 0755);
}

// Function to perform the rename operation
int test_rename(const char *base_path) {
    char src_dir[256];
    char dest_dir[256];

    snprintf(src_dir, sizeof(src_dir), "%s/d-00", base_path);
    snprintf(dest_dir, sizeof(dest_dir), "%s/d-01/d-00", base_path);

    printf("Renaming %s to %s\n", src_dir, dest_dir);
    if (rename(src_dir, dest_dir) != 0) {
        perror("rename");
        return errno;
    } else {
        printf("Successfully renamed %s to %s\n", src_dir, dest_dir);
        return 0;
    }
}

// Function to clean up the test directory structure
void clean_up(const char *base_path) {
    char sub_dir[256];
    char dest_dir[256];
    char dest_base[256];

    snprintf(sub_dir, sizeof(sub_dir), "%s/d-01/d-00/d-01", base_path);
    snprintf(dest_dir, sizeof(dest_dir), "%s/d-01/d-00", base_path);
    snprintf(dest_base, sizeof(dest_base), "%s/d-01", base_path);

    // Remove the subdirectory
    rmdir(sub_dir);

    // Remove the destination directory
    rmdir(dest_dir);

    // Remove the destination base directory
    rmdir(dest_base);
}

// Function to check if a directory exists
int dir_exists(const char *path) {
    struct stat info;

    if (stat(path, &info) != 0) {
        return 0;
    } else if (info.st_mode & S_IFDIR) {
        return 1;
    } else {
        return 0;
    }
}

// Function to compare the directory structures
int compare_structures(const char *path1, const char *path2) {
    DIR *dir1 = opendir(path1);
    DIR *dir2 = opendir(path2);

    if (dir1 == NULL || dir2 == NULL) {
        perror("opendir");
        if (dir1) closedir(dir1);
        if (dir2) closedir(dir2);
        return -1;
    }

    struct dirent *entry1, *entry2;
    int result = 1;

    while ((entry1 = readdir(dir1)) != NULL && (entry2 = readdir(dir2)) != NULL) {
        if (strcmp(entry1->d_name, ".") == 0 || strcmp(entry1->d_name, "..") == 0) {
            continue;
        }
        if (strcmp(entry2->d_name, ".") == 0 || strcmp(entry2->d_name, "..") == 0) {
            continue;
        }
        if (strcmp(entry1->d_name, entry2->d_name) != 0) {
            result = 0;
            break;
        }
    }

    closedir(dir1);
    closedir(dir2);

    return result;
}

int main() {
    const char *paths[] = {
        "/mnt/ext4-rename-test",
        "/mnt/verifs2-rename-test"
    };

    int errors[2] = {0, 0};

    for (int i = 0; i < 2; i++) {
        printf("Testing on %s\n", paths[i]);

        // Step 1: Create the initial directory structure
        create_test_structure(paths[i]);

        // Step 2: Perform the rename operation
        errors[i] = test_rename(paths[i]);

        printf("\n");
    }

    // Compare the results
    if (errors[0] == errors[1]) {
        printf("Both file systems behaved the same for the rename operation.\n");
    } else {
        printf("File systems behaved differently for the rename operation.\n");
        printf("Error on /mnt/ext4-rename-test: %s\n", strerror(errors[0]));
        printf("Error on /mnt/verifs2-rename-test: %s\n", strerror(errors[1]));
    }

    // Compare the resultant directory structures
    int structures_same = compare_structures("/mnt/ext4-rename-test/d-01/d-00", "/mnt/verifs2-rename-test/d-01/d-00");

    if (structures_same == 1) {
        printf("Resultant directory structures are the same.\n");
    } else if (structures_same == 0) {
        printf("Resultant directory structures are different.\n");
    } else {
        printf("Failed to compare directory structures.\n");
    }

    // Clean up
    // for (int i = 0; i < 2; i++) {
    //     clean_up(paths[i]);
    // }

    return 0;
}
