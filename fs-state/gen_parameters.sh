#!/bin/bash

write_offset_start=0
write_offset_stop=65536
write_offset_step=5120

write_size_start=0
write_size_stop=32768
write_size_step=6144

write_byte_start=1
write_byte_stop=255
write_byte_step=1

truncate_len_start=0
truncate_len_stop=260000
truncate_len_step=30000

gen_inline() {
    name=$1
    startname=${name}_start
    stopname=${name}_stop
    stepname=${name}_step
    start=${!startname}
    stop_=${!stopname}
    step=${!stepname}
    echo "inline pick_$name(value) {"
    echo "    if"
    for val in $(seq $start $step $stop_); do
        echo "        :: value = $val;"
    done
    echo "    fi"
    echo "}"
}

gen_inline write_offset;
gen_inline write_size;
gen_inline write_byte;
gen_inline truncate_len;

a=`expr \( $write_offset_stop - $write_offset_start \) \/ $write_offset_step + 1`
b=`expr \( $write_size_stop - $write_size_start \) \/ $write_size_step + 1`
c=`expr \( $write_byte_stop - $write_byte_start \) \/ $write_byte_step + 1`
d=`expr \( $truncate_len_stop - $truncate_len_start \) \/ $truncate_len_step + 1`
# mkdir/rmdir creates two different states: with/without testdir */
e=2
# create/unlink creates two different states: with/without testfile */
f=2

total_states=`expr $a \* $b \* $c \* $d \* $e \* $f`
echo "There are a total of $total_states different file system states." 1>&2;

