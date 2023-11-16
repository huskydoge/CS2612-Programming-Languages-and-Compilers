# README #

这是我们课程相关文件的repo。

其中包括了两个子模块SetsClass和compcert_lib



获取本repo内容指令：

```
git clone https://bitbucket.org/WxWyashen/cs2612-aut2023.git
git submodule init
git submodule update
```

或者使用

```
git clone https://bitbucket.org/WxWyashen/cs2612-aut2023.git
git submodule update --init --recursive
```



repo和子模块内提供了相关的Makefile和_CoqProject用于整个项目文件的编译。

windows需要自行提供CONFIGURE文件用于提供相关依赖的地址，以cygwin编译环境下的CONFIGURE设置为例：

```
COQBIN=/cygdrive/d/Coq-8.12/bin/
```

其中COQBIN是coq安装的位置。



在编译之前需要先通过make depend生成对应的依赖，然后再进行make。