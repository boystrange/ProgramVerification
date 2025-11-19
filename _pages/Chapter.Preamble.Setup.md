---
title: Setup
prev:  Chapter.Preamble.Demo
---

<!--
<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="Chapter.Preamble.Setup.html" class="Module">Chapter.Preamble.Setup</a> <a id="95" class="Keyword">where</a>
</pre>-->

The best way to use Agda requires the installation of a suitable
combination of tools, including at least Agda itself and an editor.
Unfortunately, the procedure is quite involved and it varies
substantially depending on the Operating System.  Below are some
instructions originally written by [Peter Selinger and Frank
Fu](https://www.mathstat.dal.ca/~selinger/agda-lectures/) to install
Agda and Emacs on [Linux](#linux), [Mac OS](#mac-os) and [Windows
10](#windows-10). At the bottom of the page is a simple [sanity
check](#sanity-check) to verify whether the installation has been
successful.

Before following these instructions, it may be worth having a look
at the [Agda
documentation](https://agda.readthedocs.io/en/latest/getting-started/installation.html#prebuilt-packages)
in case there are more up-to-date and/or specific installation
procedures for your Operating System. In particular, Agda is known
to work reasonably well also in combination with [Visual Studio
Code](https://code.visualstudio.com), which is a more
"modern-looking" editor compared to Emacs.

There are also two faster ways of getting started using Agda out of
the box without installing it, but both have shortcomings. One is to
use [this online service](https://agdapad.quasicoherent.io/). The
problems of this service are that its availability may not be
guaranteed in the future and its use may be limited to "simple" Agda
programs. Another way is to use a [Virtual Box
image](https://zenodo.org/record/4527309) of Ubuntu that comes with
pre-installed and pre-configured Agda, Emacs and Visual Studio
Code. Using this image requires a one-time installation of [Virtual
Box](https://www.virtualbox.org). Installing the image guarantees
persistent availability of Agda on your machine, but its execution
may be occasionally slow and/or stuttering because of the
virtualization.

## Linux

These instructions are for [Ubuntu](https://ubuntu.com) and derived
distributions. Analogous instructions might work on other Linux
distributions. If you can, make sure that you have a sufficiently
recent version of Linux. For example, Ubuntu 20.04 comes with Agda
2.6. Older versions of Ubuntu may come with older Agda versions,
which may or may not lead to problems.

1. Install Emacs using the package manager of your distribution.
   E.g., in Ubuntu, you can enter the following in the terminal.

   ```bash
   sudo apt update
   sudo apt install emacs
   ```

2. Install Agda using your package manager.  E.g., in Ubuntu, you
   can enter the followings in the terminal.

   ```bash
   sudo apt install agda
   ```

   Perhaps you also need this, but with Ubuntu 20.10, this package is
   not needed:

   ```bash
   sudo apt install agda-mode
   ```

3. Create a `.emacs` file in your home directory and paste the
   following text to it.

   ```elisp
   (load-file (let ((coding-system-for-read 'utf-8))
          (shell-command-to-string "agda-mode locate")))
   ```

## Mac OS

1. Install [Homebrew](https://brew.sh).

2. Install Emacs. In the terminal, enter the following:

   ```bash
   brew install --cask --no-quarantine emacs
   ```

   Note: now you should be able to find Emacs in your `/Application`
   folder.  If double clicking the icon does not open it because "Apple
   cannot check it for malicious software", right-click on the icon and
   click open. After this, Emacs should be opened alright.

3. Install Agda.  In the terminal, enter the following:

   ```bash
   brew install agda
   ```

   Now if you enter `agda --version`, you should see something like
   `Agda version 2.6.2.2` (or a more recent version, depending on which
   one you have installed).

4. Set up Agda.  In the terminal, enter the following:

   ```bash
   agda-mode setup
   ```

## Windows 10

The installation may fail if your Windows username contains a
space. If this is the case, create a new user, make them an admin
user, and then follow the below instructions as that user.

### Install Emacs

Emacs is a text editor and Agda requires it. Download the [installer
for emacs 28.1 (or a more recent
version)](http://mirror.team-cymru.com/gnu/emacs/windows/).  Once
the downloading is finished, you can install Emacs by double
clicking the executable file and following the instructions.

### Install Haskell and Agda

1. Open the Powershell.

2. [Install **Haskell**](https://www.haskell.org/ghcup/).

3. Close and reopen the Powershell.  You can type `ghc -v` and hit
   enter. You should see something like "Glasgow Haskell Compiler,
   version 8.10.3".

4. Enter `cabal update`.

5. Enter `cabal install Agda` to install Agda.  This will take quite
   some time (possibly more than 30 minutes, depending on the
   configuration of the PC).

### Configure Emacs and Agda mode

1. In the Powershell, enter the following command, replacing `name`
   with your own username.

   ```posh
   $env:Path += ";C:\Users\name\AppData\Roaming\cabal\bin"
   ```

2. Now if you enter `agda --version` in the Powershell, you should see
   something like "Agda version 2.6.2.1".

3. Enter the following command, replacing `name` with your own
   username.

   ```posh
   echo "" >> C:\Users\name\AppData\Roaming\.emacs
   ```

   The above will create an empty file with the name `.emacs` under
   the specified directory.

4. Open the above `.emacs` file using the installed Emacs editor.
   Paste the following code to the file, save it and close Emacs.
   (Use `Ctrl-X` followed by `Ctrl-S` to save, and `Ctrl-X` followed
   by `Ctrl-C` to close Emacs).

   ```elisp
   (setq exec-path (append exec-path '("C:\\cabal\\bin")))
   (load-file (let ((coding-system-for-read 'utf-8))
          (shell-command-to-string "C:\\cabal\\bin\\agda-mode locate")))
   ```

## Sanity Check

To check that the installation was successful, create an empty file
called `nat.agda` and open it in Emacs. Paste the following Agda
code to the file.

<pre class="Agda"><a id="6017" class="Keyword">data</a> <a id="Nat"></a><a id="6022" href="Chapter.Preamble.Setup.html#6022" class="Datatype">Nat</a> <a id="6026" class="Symbol">:</a> <a id="6028" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="6032" class="Keyword">where</a>
  <a id="Nat.Z"></a><a id="6040" href="Chapter.Preamble.Setup.html#6040" class="InductiveConstructor">Z</a> <a id="6042" class="Symbol">:</a> <a id="6044" href="Chapter.Preamble.Setup.html#6022" class="Datatype">Nat</a>
  <a id="Nat.S"></a><a id="6050" href="Chapter.Preamble.Setup.html#6050" class="InductiveConstructor">S</a> <a id="6052" class="Symbol">:</a> <a id="6054" href="Chapter.Preamble.Setup.html#6022" class="Datatype">Nat</a> <a id="6058" class="Symbol">-&gt;</a> <a id="6061" href="Chapter.Preamble.Setup.html#6022" class="Datatype">Nat</a>
</pre>
Notice that there is no color for the above Agda code after you
pasted it.  Now type `Ctrl-C` followed by `Ctrl-L` in Emacs. This
will color the above Agda code, confirming that Agda has
successfully checked its validity.

## Homework

1. Install and setup Agda.
