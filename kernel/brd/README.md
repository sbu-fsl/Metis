## Building the kernel module

```bash
make -C /lib/module/$(uname -r)/build M=$(pwd)
```

## Install the module

```bash
sudo insmod brd.ko rd_nr=N, rd_sizes=size1,size2,size3,...,sizeN
```
