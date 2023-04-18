#!/bin/sh

DIRM=`pwd`

DIRM_L="$DIRM/../libs"

SAT4J_DIR="$DIRM_L/org.sat4j.core.jar"

LOGICNG_DIR="$DIRM_L/logicng-2.4.1.jar"

ANTLR_DIR="$DIRM_L/antlr-runtime-4.9.3.jar"

CLASSPATH=".:$CLASSPATH:$DIRM:$DIRM_L:$SAT4J_DIR:$LOGICNG_DIR:$ANTLR_DIR"

export CLASSPATH

javac *.java

java A3main $*


