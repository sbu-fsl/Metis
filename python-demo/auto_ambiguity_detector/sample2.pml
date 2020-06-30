if 
    ::(offset >= file_len) -> {
        printf("Case 2: offset over file len, skip reading\n")
        qreply ! NFS4_OK, true, 0, nondata;
        goto read_success
        }
    ::(offset + count < file_len) -> {
        printf("Case 3: legit reading, full reading, process the request\n")
        /* full read: read count bytes at cfh offset and send to qreply */
        run FILE_BYTES(qreply, cfh, false, offset, count);
        goto read_success
    }
    /* AMBIGUITY 2: need "offset < file_len" check */
    ::(offset + count >= file_len) -> {
        printf("Case 4: legit reading, partial reading, processs the request\n");
        /* partial read: read actual bytes at cfh offset and send to qreply */
        run FILE_BYTES(qreply, cfh, true, offset, file_len - offset + count);
        goto read_success
    }
fi