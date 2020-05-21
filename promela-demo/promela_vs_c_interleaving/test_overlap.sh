#!/bin/bash

sudo ./pan | grep -E 'BEGIN|END' | while read -r line1; do
    A=`echo $line1 | cut -d ']' -f 2`;
    read -r line2;
    B=`echo $line2 | cut -d ']' -f 2`;
    BEGIN=`echo $A | cut -d ':' -f 1`;
    END=`echo $B | cut -d ':' -f 1`;
    OP1=`echo $A | cut -d ':' -f 2`;
    OP2=`echo $B | cut -d ':' -f 2`;

    if [ "$BEGIN" = "BEGIN" ] && [ "$END" = "END" ] && [ "$OP1" = "$OP2" ]; then
        echo "OK: BEGIN - $OP1/$OP2 - END";
    else
        echo "INTERLEAVING: $line1; $line2";
    fi
done
