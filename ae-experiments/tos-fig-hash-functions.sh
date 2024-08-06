#!/bin/bash


# Define the SPIN hash function file path
SPIN_PATH="$HOME/fsl-spin"
FILE_PATH="$SPIN_PATH/Src/pangen2.c"
DEFAULT_HASH_METHOD=2

HASH_TYPES=("XXH128" "XXH3-64" "MD5" "CRC32")

######### For each hash algorithm: Loop through numbers 0 to 3
for i in {0..3}; do
    ############# Step 1: Edit the SPIN file and recompile #############
    # Use sed to replace the number 2 with the current number
    sed -i "s/int absfs_hash_method = [0-9]\+;/int absfs_hash_method = $i;/" "$FILE_PATH"
    
    # Optionally, print a message indicating the change
    echo "Changed absfs_hash_method to $i (${HASH_TYPES[$i]}) in $FILE_PATH"

    # Recompile the SPIN
    cd $SPIN_PATH
    git checkout c-track-hooks
    make clean
    make
    sudo make install

    ############# Step 2: Run the SPIN tests #############
done

# Restore to the default hash method
sed -i "s/int absfs_hash_method = [0-9]\+;/int absfs_hash_method = $DEFAULT_HASH_METHOD;/" "$FILE_PATH"
echo "All completed."
