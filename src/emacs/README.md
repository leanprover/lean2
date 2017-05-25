Emacs mode for the [Lean 2 theorem prover][Lean2]. ``lean-mode`` requires [Emacs 24][emacs24]

[Lean2]: https://github.com/leanprover/lean2

Installation
============

Open your emacs init file. Do this by running Emacs and go to the file using <kbd>C-c C-f</kbd>
(control-C, control-F) and then entering ``~/.emacs``. Now paste the following code into this file (assuming you built Lean from source).

Note: You paste text in Emacs using <kbd>C-y</kbd> (control-Y). See [this wiki page][emacs-copy-paste]. See [this reference sheet][emacs-ref] for other basic Emacs commands.

[emacs-ref]: https://www.emacswiki.org/emacs/EmacsNewbieKeyReference
[emacs-copy-paste]: https://www.emacswiki.org/emacs/CopyAndPaste

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

;; Set up lean-root path
(setq lean-rootdir "~/projects/lean2")  ;; <=== YOU NEED TO MODIFY THIS
(setq-local lean-emacs-path
            (concat (file-name-as-directory lean-rootdir)
                    (file-name-as-directory "src")
                    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```

Then modify the directory in `(setq lean-rootdir "~/projects/lean2")` to your Lean folder. Now close Emacs <kbd>C-x C-c</kbd> and open Emacs again.
Emacs will install all required packages now for you.

If you didn't build Lean 2 from source, but installed it, replace `;; Set up lean-root path` and everything below with the following snippets, depending on how you got Lean 2.


Installed Lean 2 via apt-get on Ubuntu or via dpkg on Debian
----------------------------------------------------------------
```elisp
;; Set up lean-root path
(setq lean-rootdir "/usr")
(setq-local lean-emacs-path "/usr/share/emacs/site-lisp/lean")
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)
```


Installed Lean 2 via homebrew on OS X
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

Installed Lean 2 in Windows
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
Emacs mode line (at the bottom of the window) when you open a file with extension `.lean` (for the
standard Lean mode) or `.hlean` (for hott mode).

If you create a new Lean file, you have to create a `.project` file in that folder:
- open a `.lean` or `.hlean` file
- go to menu-bar (top of screen) -> Lean -> Create a new project
- click open
- it will ask "standard or hott": type which mode you want to use and press enter
- Go back to your `.lean` or `.hlean` file (you can close the `.project` file using <kbd>C-x k RET</kbd> (RET is enter)). You might need to close and reopen Emacs for the error messages to disappear.

You can check a file using the shortcut <kbd>C-c C-x</kbd>. There is also on-the-fly checking, if you type in a new file
```lean
print id
```
the word ``print`` will be underlined, and hovering over it will show
you the type of ``id``. The mode line will show ``FlyC:0/1``, indicating
that there are 0 errors and 1 message. Whenever
you type, an asterisk should briefly appear after ``FlyC``, indicating that
your file is being checked.

Some unicode characters might look weird (or make a line very high). See below to fix that.

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
------------------------------------

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

(require 'ido)
(ido-mode t)
(setq completion-ignored-extensions
       (append '(".ilean" ".olean" ".clean" ".d") completion-ignored-extensions))

```

Known Issues and Possible Solutions
===================================

Unicode
-------

If you experience a problem rendering unicode symbols on emacs,
please download the following fonts and install them on your machine:

 - [Dejavu Fonts](https://sourceforge.net/projects/dejavu/files/dejavu/2.37/dejavu-fonts-ttf-2.37.tar.bz2/download)

Alternatively, download:

 - [Quivira.ttf](http://www.quivira-font.com/files/Quivira.ttf)
 - [NotoSans](https://github.com/googlei18n/noto-fonts/blob/master/hinted/NotoSans-Regular.ttc?raw=true)
 - [NotoSansSymbols](https://github.com/googlei18n/noto-fonts/blob/master/unhinted/NotoSansSymbols-Regular.ttf?raw=true)

Then, have the following lines in your emacs setup to use `DejaVu Sans Mono` font:

```elisp
(when (member "DejaVu Sans Mono" (font-family-list))
  (set-face-attribute 'default nil :font "DejaVu Sans Mono-11"))
```

Also install [emacs-unicode-fonts](https://github.com/rolandwalker/unicode-fonts) package.

 - Run `M-x package-refresh-contents`, `M-x package-install`, and type `unicode-fonts`.
 - Add the following lines in your emacs setup:

```lisp
(require 'unicode-fonts)
(unicode-fonts-setup)
```


Installing packages manually
----------------------------

If you want to install the packages manually, you can use <kbd>M-x package-install</kbd> to install the following packages:

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

Init file
---------

The init file can be found in different places on different systems:

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
