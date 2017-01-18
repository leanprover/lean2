Preparing working environment on Ubuntu 12.04
---------------------------------------------

### Install basic packages

    sudo apt-get install git
    sudo apt-get install libgmp-dev
    sudo apt-get install libmpfr-dev
    sudo add-apt-repository ppa:kalakris/cmake -y
    sudo apt-get install cmake
    sudo apt-get install liblua5.2.0 lua5.2-0 lua5.2-dev

    sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
    sudo update-alternatives --remove-all gcc
    sudo update-alternatives --remove-all g++
    sudo apt-get update
    sudo apt-get install g++-4.8 -y
    sudo apt-get upgrade -y && sudo apt-get dist-upgrade -y

### Optional packages

    sudo apt-get install gitg
    sudo apt-get install valgrind
    sudo apt-get install doxygen
    sudo apt-get install kcachegrind

    sudo add-apt-repository --yes ppa:boost-latest/ppa
    sudo apt-get install libboost1.54-dev
    sudo apt-get install libboost-thread1.54-dev

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

### Alternatively, build Lean using Boost

    cd lean2
    mkdir -p build
    cd build
    cmake -D CMAKE_BUILD_TYPE=Release -D BOOST=ON ../src
    make

### If you are using Emacs, here are some basic configurations

    (custom-set-variables
      '(c-basic-offset 4)
      '(global-font-lock-mode t nil (font-lock))
      '(show-paren-mode t nil (paren))
      '(transient-mark-mode t))


    (tool-bar-mode -1)
    (setq visible-bell t)
    (setq-default indent-tabs-mode nil)
    (setq visible-bell t)
    (column-number-mode 1)

    ;; Coding Style
    (setq auto-mode-alist (cons '("\\.h$" . c++-mode) auto-mode-alist))
    (defconst my-cc-style
      '("cc-mode"
       (c-offsets-alist . ((innamespace . [0])))))
    (c-add-style "my-cc-mode" my-cc-style)
    (add-hook 'c++-mode-hook '(lambda ()
                                 (c-set-style "my-cc-mode")
                                 (gtags-mode 1)
                                ))

    ;; C++ 11 new keywords
    (font-lock-add-keywords 'c++-mode
       '(("\\<\\(thread_local\\)\\>" . font-lock-warning-face)
        ("\\<\\(constexpr\\)\\>" . font-lock-keyword-face)
        ))

You need to also set up the [Emacs Mode](../../src/emacs/README.md).
