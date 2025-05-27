STUDENT_ID := 2018-18389

.PHONY: all install-graphviz

all:
	@command -v dot >/dev/null 2>&1 || $(MAKE) install-graphviz
	clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names test.c -o test.ll
	opt -S -passes='dot-cfg' test.ll -disable-output
	dot -Tpng .main.dot -o PR0_$(STUDENT_ID).png

install-graphviz:
	sudo apt update
	sudo apt install -y graphviz
