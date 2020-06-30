import random as rd

def getRandom():
    return rd.randrange(10000)

if __name__ == "__main__":
    for i in range(20):
        if_count = 0
        offset = getRandom()
        count = getRandom()
        file_len = getRandom()
        if(offset >= file_len):
            if_count += 1
        if(offset + count < file_len):
            if_count += 1
        if(offset + count >= file_len):
            if_count += 1
        if(if_count != 1):
            print("Ambiguity found with offset", offset, "count", count, "file_len", file_len)
            break
