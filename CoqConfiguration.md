# How to Configure Coq in Vscode for MacOS



**PC:** macbook 2021, M1 Pro chip

## Why Vscode?
* Auto-completion, which brings great convenience.
* Better arrangement of files, with graphical file structure UI.
* No problem with Chinese unicode encoding conversion failure.

**If you think CoqIDE can suit all your needs, then you can close this page now.**

## Tutorial
First we should open terminal and input following commands.
```
$ opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
$ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
$ opam pin add coq 8.18+rc1
$ opam install vscoq-language-server
```
After complete all those commands, try `where vscoqtop` and copy the path. 

Open Visual Studio Code.app, then open extensions market and search for `"vscoq"`, download `version 2.0.0`. Open "vscoq" extension setting

<img width="500" alt="vscoq" src="https://github.com/huskydoge/CS2612-Programming-Languages-and-Compilers/assets/91367324/b50dbafe-32d0-4af0-9b4f-0ef4fed35410">
<img width="500" alt="截屏2023-09-19 10 43 36" src="https://github.com/huskydoge/CS2612-Programming-Languages-and-Compilers/assets/91367324/98739bac-6259-476f-969e-28add46c5402" style="align">

## How to use (Hw1 for example)

1. Make a new directory and create file `_CoqProject` with no name extension.
2. Use vscode to open `_CoqProject` and write a line `-Q.PL` in _CoqProject
3. Input into vscode terminal:  `coq_makefile -f _CoqProject *.v -o Makefile`
4. Input into vscode terminal: `make`
5. Restart vscode
6. Open your `file.v` ( for example `hw1.v`), and you can see all the libraries are imported successfully.

<div align="center">
<img width="500" alt="hw1" src="https://github.com/huskydoge/CS2612-Programming-Languages-and-Compilers/assets/91367324/83941b4a-b6c3-4a78-b008-249fd6f03121">
<img width="500" alt="mode" src="https://github.com/huskydoge/CS2612-Programming-Languages-and-Compilers/assets/91367324/7580f261-5634-4a75-9569-65b3369f879e">
</div>

7. Write your code and complete the work. If you want to change the proof mode to `Manual` ( like in CoqIDE), just change setting shown above to `Manual`. Then you could press control(⌃) + option(⌥) + ↓ / ↑ to manual prove a line.


## Reference
* https://coq.inria.fr/refman/practical-tools/utilities.html
* https://github.com/coq-community/vscoq/issues/623
* With help from TA Cheng
