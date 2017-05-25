Emacs mode for [lean theorem prover][Lean]

[lean]: https://github.com/leanprover/lean


Requirements
============

``lean-mode`` requires [Emacs 24][emacs24] and the following
packages, which can be installed via <kbd>M-x package-install</kbd>.

 - [dash][dash]
 - [dash-functional][dash]
 - [f][f]
 - [s][s]

[emacs24]: http://www.gnu.org/software/emacs
[dash]: https://github.com/magnars/dash.el
[f]: https://github.com/rejeep/f.el
[s]: https://github.com/magnars/s.el

The following packages are optional, but strongly recommended.

 - [company][company]
 - [flycheck][flycheck]
 - [fill-column-indicator][fci]

Both the optional and required packages will be installed for you
automatically the first time you use ``lean-mode``, if you follow the
installation instructions below.

[company]: http://company-mode.github.io/
[flycheck]: http://www.flycheck.org/manual/latest/index.html
[fci]: https://github.com/alpaker/Fill-Column-Indicator


Installation
============

When Emacs is started, it loads startup information from a special
initialization file, often called an "init file." The init file can be
found in different places on different systems:

- Emacs will check for a file named ``.emacs`` in your home directory.
- With GNU Emacs, it is common to use ``.emacs.d/init.el`` instead.
- With Aquamacs, it is common to use ``~/Library/Preferences/Aquamacs Emacs/Preferences.el``.

On Windows, there are two additional complications:

- It may be hard to figure out what Emacs considers to be your "home
  directory".
- The file explorer may not let you create a file named ``.emacs``,
  since it begins with a period.

One solution is to run Emacs itself and create the file using C-c C-f
(control-C, control-F) and then entering ``~/.emacs``. (The tilde
indicates your home directory.) On Windows, you can also name the file
``_emacs``.

Put the following code in your Emacs init file:

```elisp
(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.milkbox.net/packages/") t)
(when (< emacs-major-version 24)
  ;; For important compatibility libraries like cl-lib
  (add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/")))
(package-initialize)

;; Install required/optional packages for lean-mode
(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck f
            fill-column-indicator s))
(let ((need-to-refresh t))
  (dolist (p lean-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))
```

Then choose your installation method from the following scenarios, and add the corresponding code to
your init file: (note: you need to change the directory in the following code snippets to the
directory of your clone of the repository).

Case 1: Build Lean from source
-----------------------------

```elisp
;; Set up lean-root path
(setq lean-rootdir "~/projects/lean2")  ;; <=== YOU NEED TO MODIFY THIS
(setq-local lean-emacs-path
            (concat (file-name-as-directory lean-rootdir)
                    (file-name-as-directory "src")
                    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```

Case 2: Install Lean via apt-get on Ubuntu or via dpkg on Debian
----------------------------------------------------------------

```elisp
;; Set up lean-root path
(setq lean-rootdir "/usr")
(setq-local lean-emacs-path "/usr/share/emacs/site-lisp/lean")
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```


Case 3: Install Lean via homebrew on OS X
-----------------------------------------

```elisp
;; Set up lean-root path
(setq lean-rootdir "/usr/local")
(setq-local lean-emacs-path "/usr/local/share/emacs/site-lisp/lean")
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```

Note: if you install homebrew in a custom location that is not the default
location, please run `brew info lean`, and it will tell you where the
lean-mode files are located. With that information, update the
`lean-emacs-path` variable accordingly.

Case 4: Install Lean in Windows
-------------------------------
```elisp
;; Set up lean-root path
(setq lean-rootdir "\\lean-0.2.0-windows")
(setq-local lean-emacs-path "\\lean-0.2.0-windows\\share\\emacs\\site-lisp\\lean")
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```


Trying It Out
=============

If things are working correctly, you should see the word ``Lean`` in the
Emacs mode line when you open a file with extension `.lean` (for the
standard Lean mode) or `.hlean` (for hott mode). If you type
```lean
check id
```
the word ``check`` will be underlined, and hovering over it will show
you the type of ``id``. The mode line will show ``FlyC:0/1``, indicating
that there are no errors and one piece of information displayed. Whenever
you type, an asterisk should briefly appear after ``FlyC``, indicating that
your file is being checked.

If you get an error which contains `failed to lock file`, you need to create a `.project` file:
- open a `.lean` or `.hlean` file
- go to menu-bar (top of screen) -> Lean -> Create a new project
- click open
- it will ask "standard or hott": type which mode you want to use and press enter
- now it has created a project file (which manages imports and so on for files outside the library), and if you go back to your `.lean` or `.hlean` file these error messages will disappear.



Key Bindings and Commands
=========================

|Key                | Function                                                                      |
|-------------------|-------------------------------------------------------------------------------|
|<kbd>M-.</kbd>     | jump to definition in source file (lean-find-tag)                             |
|<kbd>TAB</kbd>     | tab complete identifier, option, filename, etc. (lean-tab-indent-or-complete) |
|<kbd>C-c C-k</kbd> | shows the keystroke needed to input the symbol under the cursor               |
|<kbd>C-c C-g</kbd> | show goal in tactic proof (lean-show-goal-at-pos)                             |
|<kbd>C-c C-p</kbd> | print information about identifier (lean-show-id-keyword-info)                |
|<kbd>C-c C-t</kbd> | show type (lean-show-type)                                                    |
|<kbd>C-c C-f</kbd> | replace underscore by inferred value (lean-fill-placeholder)                  |
|<kbd>C-c C-x</kbd> | execute lean in stand-alone mode (lean-std-exe)                               |
|<kbd>C-c C-l</kbd> | execute lean in stand-alone mode (lean-std-exe)                               |
|<kbd>C-c C-o</kbd> | set option (lean-set-option)                                                  |
|<kbd>C-c C-r</kbd> | restart lean process (lean-server-reset-process)                              |
|<kbd>C-c C-e</kbd> | evaluate a lean comman (lean-eval-cmd)                                        |
|<kbd>C-c ! n</kbd> | flycheck: go to next error                                                    |
|<kbd>C-c ! p</kbd> | flycheck: go to previous error                                                |
|<kbd>C-c ! l</kbd> | flycheck: show list of errors                                                 |

The Flycheck annotation `FlyC:n/n` indicates the number of errors / responses from Lean. An asterisk
`*FlyC:n/n` indicates that checking is in progress. Clicking on `FlyC` opens the Flycheck menu.

To profile Lean performace on the file in the buffer, enter <kbd>M-x lean-execute</kbd> or choose
`Lean execute` from the Lean menu, and add the option `--profile`.


Some basic configurations (optional)
====================================

```lisp
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
```

Known Issues and Possible Solutions
===================================

Unicode
-------

If you experience a problem rendering unicode symbols on emacs,
please download the following fonts and install them on your machine:

 - [Quivira.ttf](http://www.quivira-font.com/files/Quivira.ttf)
 - [Dejavu Fonts](http://sourceforge.net/projects/dejavu/files/dejavu/2.35/dejavu-fonts-ttf-2.35.tar.bz2)
 - [NotoSans](https://github.com/googlei18n/noto-fonts/blob/master/hinted/NotoSans-Regular.ttc?raw=true)
 - [NotoSansSymbols](https://github.com/googlei18n/noto-fonts/blob/master/unhinted/NotoSansSymbols-Regular.ttf?raw=true)

Then, have the following lines in your emacs setup to use `DejaVu Sans Mono` font:

```elisp
(when (member "DejaVu Sans Mono" (font-family-list))
  (set-face-attribute 'default nil :font "DejaVu Sans Mono-11"))
```

You may also need to install [emacs-unicode-fonts](https://github.com/rolandwalker/unicode-fonts) package.

 - Run `M-x package-refresh-contents`, `M-x package-install`, and type `unicode-fonts`.
 - Add the following lines in your emacs setup:

```lisp
(require 'unicode-fonts)
(unicode-fonts-setup)
```

Contributions
=============

Contributions are welcome!

If your contribution is a bug fix, create your topic branch from
`master`. If it is a new feature, check if there exists a
WIP(work-in-progress) branch (`vMAJOR.MINOR-wip`). If it does, use
that branch, otherwise use `master`.

Install [Cask](https://github.com/cask/cask) if you haven't already,
then:

    $ cd /path/to/lean/src/emacs
    $ cask

Run all tests with:

    $ make
