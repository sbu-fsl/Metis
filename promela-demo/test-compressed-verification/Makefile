# Place a memory limit for storing spaces.
# Uses bloom filters to select states.
# Use -h -k run options to  manipulate hash functions and bit set per hash function.
run_20_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w20;
run_25_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w25;
run_21_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w21;
run_22_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w22;
run_23_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w23;
run_24_bits_memory_space: example.pml
	spin -a example.pml; \
	cc -DBITSTATE -o pan pan.c ;\
	./pan -w24;
clean:
	rm -rf test test.txt pan*
