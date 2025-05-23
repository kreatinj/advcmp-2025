cd ~
git clone https://github.com/llvm/llvm-project.git
cd llvm-project
git pull
git checkout release/17.x

cd ~
mkdir -p llvm-project/build
cd llvm-project/build
cmake -G Ninja ../llvm \
  -DCMAKE_CXX_STANDARD=17 \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX="/tmp/llvm" \
  -DLLVM_ENABLE_RTTI=ON \
  -DLLVM_TARGETS_TO_BUILD="host" \
  -DLLVM_ENABLE_ASSERTIONS=ON \
  -DLLVM_BUILD_LLVM_DYLIB=ON \
  -DLLVM_DYLIB_COMPONENTS="all" \
  -DLLVM_USE_LINKER="lld" \
  -DLLVM_CCACHE_BUILD=ON

ninja
ninja install

echo "tmp/llvm/lib" | sudo tee /etc/ld.so.conf.d/llvm.conf
sudo ldconfig
