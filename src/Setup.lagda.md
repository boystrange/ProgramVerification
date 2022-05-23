---
title: Setup
---

<!--
```agda
module Setup where
```
-->

In order to use Agda it is necessary to install a suitable
combination of tools, including at least Agda itself and an
editor. The procedure varies substantially depending on the
Operating System. Below are some instructions originally written by
[Peter Selinger and Frank
Fu](https://www.mathstat.dal.ca/~selinger/agda-lectures/) to install
Agda and Emacs on [Linux](#linux), [Mac OS](#mac-os) and [Windows
10](#windows-10). While I am reasonably sure that the given
instructions for Linux and Mac OS are still valid, I have no
experience at all on installing Agda on Windows. At the bottom of
the page is a simple [sanity check](#sanity-check) to verify whether
the installation has been successful.

Before following these instructions, it may be worth having a look
at the [Agda
documentation](https://agda.readthedocs.io/en/latest/getting-started/installation.html#prebuilt-packages)
in case there are more up-to-date and/or specific installation
procedures for your Operating System. In particular, Agda is known
to work reasonably well also in combination with [Visual Studio
Code](https://code.visualstudio.com), which is a more
"modern-looking" editor compared to Emacs.

There is also an [online service](https://agdapad.quasicoherent.io/)
that can be used to try Agda without installing it. Note that the
availability of this service may not be guaranteed and that its use
may be limited to "simple" Agda programs.

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

1. Install command line tools for XCode if you haven't done so before.

   Go to
   [https://developer.apple.com/download/more/](https://developer.apple.com/download/more/)
   and download the DMG file for command line tools for XCode 12.3 (or
   a more recent version). You will be asked to use your Apple
   credentials to sign in.  Once you have downloaded the DMG file,
   double click to install as usual.

2. Install [Home Brew](https://brew.sh).  Open a terminal and enter the
   following:

   ```bash
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
   ```

3. Install Emacs. In the terminal, enter the following:

   ```bash
   brew install --cask --no-quarantine emacs
   ```

   Note: now you should be able to find Emacs in your `/Application`
   folder.  If double clicking the icon does not open it because "Apple
   cannot check it for malicious software", right-click on the icon and
   click open. After this, Emacs should be opened alright.

4. Install Agda.  In the terminal, enter the following:

   ```bash
   brew install agda
   ```

   Now if you enter `agda --version`, you should see something like
   `Agda version 2.6.1.2` (or a more recent version, depending on which
   one you have installed).

5. Set up Agda.  In the terminal, enter the following:

   ```bash
   agda-mode setup
   ```

## Windows 10

Note: it has been found that the installation will fail if your
Windows username contains a space. If this is the case, create a new
user, make them an admin user, and then follow the below
instructions as that user.

Install Emacs. Emacs is a text editor and Agda requires it.

Download the [emacs-27-x86_64
installer](http://mirror.team-cymru.com/gnu/emacs/windows/).  Once
the downloading is finished, you can install Emacs by double
clicking the executable file and following the instruction.

Install the Haskell platform and Agda. Agda runs on the Haskell
platform.

1. Type `powershell` in the Windows search prompt, and right click
   on the Powershell app and "run as administrator".

2. Copy and paste the following command to the Powershell and type
   return.

   ```posh
   Set-ExecutionPolicy Bypass -Scope Process -Force; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1'))
   ```

   The above command will install the `choco` command. If the
   installation went well, you can type `choco` in the commandline
   and you should see something like "Chocolatey v0.10.15"

3. Type `choco install haskell-dev` and hit enter. This will install
   the Haskell platform.  You may be asked for permission to run
   some scripts, just type `A` to say yes to all.  It may take
   several minutes to finish the installation.  Then type
   `refreshenv` and hit enter.

4. Now you have installed the Haskell platform. Now close the
   Powershell.

5. Open the Powershell again (do not run it as administrator this
   time).  You can type `ghc -v` and hit enter. You should see
   something like "Glasgow Haskell Compiler, version 8.10.3"

6. Enter `cabal update`.

7. Enter `cabal install Agda-2.6.1.1` to install Agda.  This will
   take 30 minutes or so.

Now configure Emacs and Agda mode.

1. In the Powershell, enter the following command (please replace
   'name' with your own username):

   ```posh
   $env:Path += ";C:\Users\name\AppData\Roaming\cabal\bin"
   ```

   Then follow with the following command:

   ```posh
   [Environment]::SetEnvironmentVariable("INCLUDE", $env:INCLUDE, [System.EnvironmentVariableTarget]::User)
   ```

2. Now if you enter `agda` in the Powershell, you should see
   something like "Agda version 2.6.1.1".

3. Enter the following command (please replace 'name' with your own
   username).

   ```posh
   echo "" >> C:\Users\name\AppData\Roaming\.emacs
   ```

   The above will create an empty file with the name `.emacs` under
   the specified directory.

4. Open the above `.emacs` file using the installed Emacs editor.
   Paste the following code to the file, save it and closed Emacs.
   (Use `Ctrl-X` followed by `Ctrl-S` to save, and `Ctrl-X` followed
   by `Ctrl-C` to close Emacs).

   ```emacs
   (load-file (let ((coding-system-for-read 'utf-8))
          (shell-command-to-string "agda-mode locate")))
   ```

## Sanity Check

To check that the installation was successful, create an empty file
called `nat.agda` and open it in Emacs. Paste the following Agda
code to the file.

```agda
data Nat : Set where
  Z : Nat
  S : Nat -> Nat
```

Notice that there is no color for the above Agda code after you
pasted it.  Now type `Ctrl-C` followed by `Ctrl-L` in Emacs. This
will color the above Agda code, confirming that Agda has
successfully checked its validity.

## Exercises

1. Install and setup Agda.
