run_atomic: atomic.pml
	spin -a atomic.pml; \
	cc -o pan pan.c; \
	./pan;
run_dstep: d_step.pml
	spin -a d_step.pml; \
	cc -o pan pan.c; \
	./pan;
run_non-deterministic_atomic:atomic_with_blocking_stmnt.pml
	spin -a atomic_with_blocking_stmnt.pml;
	cc -o pan pan.c; \
	./pan;
clean:
	rm -rf pan*
