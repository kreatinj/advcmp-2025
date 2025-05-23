.PHONY: all

BUILD_DIR := build

all: build
	cmake --build $(BUILD_DIR)
	clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone -Xclang -disable-llvm-passes -fno-discard-value-names test.c -o test.ll
	opt -S -passes='mem2reg' test.ll -o input.ll
	opt -S -load-pass-plugin='$(BUILD_DIR)/lib/libSimpleSCCP.so' -passes='print<simple-sccp>' input.ll -disable-output 2> test.out

build:
	cmake -S . -G Ninja -B $(BUILD_DIR)
