.PHONY: test submit

test.ll:
	clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone -fno-discard-value-names test.c -o test.ll

test.out: test.ll
	opt -S -load-pass-plugin='../build/lib/libInstructionCounter.so' -passes='instruction-counter' test.ll -disable-output 2> test.out

test: test.out
