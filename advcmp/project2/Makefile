.PHONY: all build clean re generate-ir run-mem2reg-pass call-pass-from-opt

BUILD_DIR := build

all: test.out

build:
	@if [ ! -d $(BUILD_DIR) ]; then \
		cmake -S . -G Ninja -B $(BUILD_DIR); \
	fi
	cmake --build $(BUILD_DIR)

clean:
	rm -rf $(BUILD_DIR)

re: clean build

test.ll:
	make generate-ir

input.ll:
	make run-mem2reg-pass

test.out:
	make call-pass-from-opt

generate-ir: build test.c
	clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone -Xclang -disable-llvm-passes -fno-discard-value-names test.c -o test.ll

run-mem2reg-pass: test.ll
	opt -S -passes='mem2reg' test.ll -o input.ll

call-pass-from-opt: input.ll
	opt -S -load-pass-plugin='$(BUILD_DIR)/lib/libSimpleSCCP.so' -passes='print<simple-sccp>' input.ll -disable-output 2> test.out
