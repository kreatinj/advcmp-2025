.PHONY: all build clean re generate-ir execute-plugin

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

test.out:
	make execute-plugin

generate-ir: build test.c
	clang -O0 -S -emit-llvm -Xclang -disable-O0-optnone -fno-discard-value-names test.c -o test.ll

execute-plugin: test.ll
	opt -S -load-pass-plugin='$(BUILD_DIR)/lib/libInstructionCounter.so' -passes='instruction-counter' test.ll -disable-output 2> test.out

