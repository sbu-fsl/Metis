#!/bin/bash

checkpoint(){

    key=$1
    sudo zfs snapshot -r mcfszpool/fs1@testsnap$1
    ret=$?
    #gets the second snapshot.

    ss1=$(zfs list -t snapshot -o name | grep mcfszpool/fs1@testsnap | tac | sed -n '2 p')

    if [ "$ss1" != "" ]; then 
        sudo zfs send -i $ss1 mcfszpool/fs1@testsnap$key | sudo  zfs recv -F zpooltest/fs
    else
        sudo zfs send -i mcfszpool/fs1@testsnap_dummy  mcfszpool/fs1@testsnap$key | sudo  zfs recv zpooltest/fs
    fi
    
    ret=$?
    
    if [[ "$ss1" != ""  && ! "$ss1" =~ "testsnap_dummy" ]]; then 
        sudo zfs destroy $ss1
    fi

    return 0

}
	
restore_v2(){
    
    #error on exit ? or return in the end?
    #sudo zfs destroy -r mcfszpool/fs1
    sudo zfs rollback -r zpooltest/fs@testsnap$1
    #ret=$?
    #if [ $ret != 0 ]; then
    #    echo "returning from here"
	#return $ret
    #fi

    #sudo zfs rollback -r zpooltest/fs@testsnap$1
    sudo zfs rollback -r mcfszpool/fs1@testsnap_dummy

    ret=$?
    if [ $ret != 0 ]; then
	return $ret
    fi
    #sleep 2
    #zfs list -t all
    #set -x
    #sudo zfs destroy mcfszpool/fs1@testsnap$1
    #ret=$?
    #if [ $ret != 0 ]; then
	#return $ret
    #fi

    sudo zfs destroy zpooltest/fs@testsnap$1
    #sleep 2
    #set +x
    #sending top one from 
    top_snapshot=$(zfs list -t snapshot -o name | grep zpooltest/fs@testsnap | tail -n 1)
    echo "TOP SNAPSHOT IS $top_snapshot"
    #zfs holds mcfszpool/fs1@testsnap$1 1>&2
    #umount -l /mnt/test-zfs
    #zfs umount mcfszpool/fs1
    #sudo zfs destroy -r mcfszpool/fs1
    #set -x
    sudo zfs send -i zpooltest/fs@testsnap_dummy $top_snapshot  | sudo  zfs recv mcfszpool/fs1
    #sudo zfs send -i mcfszpool/fs1testsnap_dummy $top_snapshot  | sudo  zfs recv zpooltest/fs

    #zfs list -t all  >> incrementalsend_err_file
    ret=$?
    #sudo zfs send $top_snapshot  | sudo  zfs recv -F mcfszpool/fs1
    #set -x
    #ps -elf > incrementalsend_err_file
    #fuser /mnt/test-zfs >> incrementalsend_err_file
    #set +x
    #echo $?
    #set +x
    #zfs set mountpoint /mnt/test-zfs mcfszpool/fs1
    #zfs mount mcfszpool/fs1
    #mount -t zfs mcfszpool/fs1 /mnt/test-zfs
    #ret=$?
    #if [ $ret != 0 ]; then
        
    #    ps -elf | grep zfs
    #    lsof /mnt/test-zfs
#	return $ret
#    fi
    
    return 0;
}

restore(){
   restore_key=$1
   top_snapshot="zpooltest/fs@testsnap$1"
   

   cmd="zfs list -t snapshot -o name | grep -B 1 zpooltest/fs@testsnap$restore_key | head -n 1"
   #second_snapshot= $(zfs list -t snapshot -o name | grep -B 1 zpooltest/fs@testsnap$restore_key | head -n 1)
   second_snapshot=$(eval "$cmd")
   if [[ $second_snapshot != "" ]]; then
       sudo zfs rollback -r mcfszpool/fs1@testsnap_dummy
       
       sudo zfs send -i zpooltest/fs@testsnap_dummy $second_snapshot | sudo  zfs recv mcfszpool/fs1
       sudo zfs send -i $second_snapshot $top_snapshot | sudo  zfs recv mcfszpool/fs1
       sudo zfs rollback -r $top_snapshot
       sudo zfs destroy $top_snapshot

       sudo zfs rollback -r mcfszpool/fs1@testsnap$restore_key
       sudo zfs destroy  mcfszpool/fs1@testsnap$restore_key
   else
       sudo zfs rollback -r mcfszpool/fs1@testsnap_dummy
       sudo zfs rollback -r zpooltest/fs@testsnap_dummy
   fi
}

#sudo ./setup.sh -s
#checkpoint 1
#checkpoint 2
#checkpoint 3
#checkpoint 4
#checkpoint 5
#restore 5

#sudo zpool destroy mcfszpool

#zfs list -t all 1>&2 

if [ $1 == "c" ]; then
    checkpoint $2
else
    restore $2
fi
