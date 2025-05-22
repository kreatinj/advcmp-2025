STUDENT_ID := 2018-18389

.PHONY: all emit-llvm-ir call-dot-ctg-pass convert-dot-into-image

all: PR0_$(STUDENT_ID).png

test.ll:
	emit-llvm-ir

.main.dot:
	make call-dot-ctg-pass

PR0_$(STUDENT_ID).png:
	make convert-dot-into-image

emit-llvm-ir: test.c
	clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names test.c -o test.ll

call-dot-ctg-pass: test.ll
	opt -S -passes='dot-cfg' test.ll -disable-output

convert-dot-into-image: .main.dot
	dot -Tpng .main.dot -o PR0_$(STUDENT_ID).png
