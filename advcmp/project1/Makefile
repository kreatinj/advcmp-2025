.PHONY: all

BUILD_DIR := build

all: build
	cmake --build $(BUILD_DIR)
	clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone -fno-discard-value-names test.c -o test.ll
	opt -S -load-pass-plugin='$(BUILD_DIR)/lib/libInstructionCounter.so' -passes='instruction-counter' test.ll -disable-output 2> test.out

build:
	cmake -S . -G Ninja -B $(BUILD_DIR)
