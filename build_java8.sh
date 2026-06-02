#!/usr/bin/env bash
# build_java8.sh — compile the TaintListener/TaintTag sources with Java 8 and
# update jpf-symbc.jar.  Run this instead of plain 'ant build' whenever you
# edit TaintListener.java or TaintTag.java.
#
# Why: the system default javac may be Java 11+, which produces class file
# version 55.  JPF requires class file version 52 (Java 8) to load its
# listener classes.  Plain 'ant build' respects source/target=8 but the class
# file version is still controlled by the compiler that javac links against.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
JAVA8_HOME="${JAVA8_HOME:-/usr/lib/jvm/java-8-openjdk-amd64}"
JAVA8_JAVAC="$JAVA8_HOME/bin/javac"
JAVA8_JAVAP="$JAVA8_HOME/bin/javap"
CORE="$SCRIPT_DIR/../jpf-core"

if [ ! -x "$JAVA8_JAVAC" ]; then
    echo "ERROR: Java 8 javac not found at $JAVA8_JAVAC" >&2
    echo "  Set JAVA8_HOME to your JDK 8 installation." >&2
    exit 1
fi

# Build classpath: compiled main dir + all lib jars + jpf-core classes
CP="$SCRIPT_DIR/build/main"
for j in "$SCRIPT_DIR/lib/"*.jar; do
    [ -f "$j" ] && CP="$CP:$j"
done
CP="$CP:$CORE/build/jpf.jar:$CORE/build/main"

SOURCES=(
    "$SCRIPT_DIR/src/main/gov/nasa/jpf/symbc/TaintListener.java"
    "$SCRIPT_DIR/src/main/gov/nasa/jpf/symbc/TaintTag.java"
)

echo "Compiling taint sources with $("$JAVA8_JAVAC" -version 2>&1) ..."
"$JAVA8_JAVAC" -source 8 -target 8 -Xlint:-options \
    -cp "$CP" -d "$SCRIPT_DIR/build/main" "${SOURCES[@]}"

echo "Updating jpf-symbc.jar ..."
jar uf "$SCRIPT_DIR/build/jpf-symbc.jar" \
    -C "$SCRIPT_DIR/build/main" gov/nasa/jpf/symbc/TaintListener.class \
    -C "$SCRIPT_DIR/build/main" gov/nasa/jpf/symbc/TaintTag.class

MAJOR=$("$JAVA8_JAVAP" -verbose \
    "$SCRIPT_DIR/build/main/gov/nasa/jpf/symbc/TaintListener.class" 2>&1 \
    | grep "major version" | awk '{print $NF}')
echo "Done. TaintListener.class major version: $MAJOR (52 = Java 8 ✓)"
if [ "$MAJOR" != "52" ]; then
    echo "WARNING: unexpected class file version — JPF may refuse to load it." >&2
    exit 1
fi
