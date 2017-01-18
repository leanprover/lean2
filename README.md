This is a snapshot of the Lean 0.2 theorem prover.
We have this separate repository because this version has special support for Homotopy Type Theory.

About
-----
- [Latest version](https://github.com/leanprover/lean)
- [Homepage](http://leanprover.github.io)
- Theorem Proving in Lean: [HTML](http://leanprover.github.io/tutorial/index.html), [PDF](http://leanprover.github.io/tutorial/tutorial.pdf)
- [Standard Library](library/library.md)
- [HoTT Library](hott/hott.md)
- [Emacs Mode](src/emacs/README.md)

Requirements
------------

- C++11 compatible compiler: [g++](http://gcc.gnu.org/) (version >= 4.8.1), or [clang++](http://clang.llvm.org/cxx_status.html) (version >= 3.3)
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)
- [MPFR (GNU MPFR Library)](http://www.mpfr.org/)
- [Lua 5.2 or 5.1](http://www.lua.org), or [LuaJIT 2.0](http://luajit.org)
- (optional) [gperftools](https://code.google.com/p/gperftools/)
- (optional) [Boost](http://www.boost.org) (version >= 1.54), we can
  build Lean using boost::thread instead of std::thread. When using
  Boost, Lean can modify the thread stack size.

Installing required packages at
--------------------------------

_Windows_

- [MSys2](doc/make/msys2.md)

_Linux_

- [Ubuntu 12.04 or newer](doc/make/ubuntu-12.04.md)
- [Ubuntu 12.04 or newer (detailed)](doc/make/ubuntu-12.04-detailed.md)
- [Fedora 19](doc/make/fedora-19.md)

_OS X_

- [OS X 10.9](doc/make/osx-10.9.md)

Build Instructions
------------------

- [CMake + Make](doc/make/cmake_make.md)
- [CMake + Ninja](doc/make/cmake_ninja.md)
- [Faster builds with ccache](doc/make/ccache.md)

Miscellaneous
-------------

- Building Doxygen Documentation: `doxygen src/Doxyfile`
- [Coding Style](doc/coding_style.md)
- [Library Style Conventions](doc/lean/library_style.org)
- [Git Commit Conventions](doc/commit_convention.md)
- [Syntax Highlight Lean Code in LaTeX](extras/latex/lstlean.md)
