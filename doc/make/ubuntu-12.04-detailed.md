Preparing working environment on Ubuntu 12.04
---------------------------------------------

### Install basic packages

    sudo apt-get install git libgmp-dev libmpfr-dev emacs -y
    sudo add-apt-repository ppa:kalakris/cmake -y
    sudo apt-get install cmake liblua5.2.0 lua5.2-0 lua5.2-dev -y

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install g++-4.8 -y
    sudo apt-get upgrade -y && sudo apt-get dist-upgrade -y

### Optional packages

    sudo apt-get install gitg ninja-build valgrind doxygen kcachegrind

    sudo add-apt-repository --yes ppa:boost-latest/ppa
    sudo apt-get install libboost1.54-dev libboost-thread1.54-dev

### Fork Lean on github : https://github.com/leanprover/lean2

### Create a projects directory

    cd ~
    mkdir projects
    cd projects

### Clone your fork

    git clone https://github.com/[your-user-name]/lean2.git

### Build Lean in release mode

    cd lean2
    mkdir -p build
    cd build
    cmake -D CMAKE_BUILD_TYPE=Release ../src
    make

### Alternative ways to build
Using Ninja (to speed up build)

    cmake -DCMAKE_BUILD_TYPE=RELEASE -G Ninja ../src
    ninja

Using Boost (to speed up build)

    cmake -D CMAKE_BUILD_TYPE=Release -D BOOST=ON ../src
    make

Build in debug mode

    cmake -DCMAKE_BUILD_TYPE=DEBUG ../src
    make
 
### You need to also set up the [Emacs Mode](../../src/emacs/README.md).
