#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
MCM_DIR=$SCRIPT_DIR/../mcm
JAVA_FLAGS="--enable-native-access=ALL-UNNAMED"

echo "Running Alloy tests..."

echo "Running test_paper_ex.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c forbidden -f $MCM_DIR/test_paper_ex.als
echo "Expected Output: UNSAT (outcome impossible)"
echo ""

echo "Running test_mp.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c allowed -f $MCM_DIR/test_mp.als
echo "Expected Output: SAT (outcome possible)"
echo ""

echo "Running test_mp_rmw.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c forbidden -f $MCM_DIR/test_mp_rmw.als
echo "Expected Output: UNSAT (outcome impossible)"
echo ""

echo "Running test_wbrace.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c race -f $MCM_DIR/test_wbrace.als
echo "Expected Output: SAT (race found)"
echo ""

echo "Running test_wbflush.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c no_race -f $MCM_DIR/test_wbflush.als
echo "Expected Output: UNSAT (no race found)"
echo ""

java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c forbidden -f $MCM_DIR/test_wbflush.als
echo "Expected Output: UNSAT (outcome impossible)"
echo ""

echo "Running test_hatsr.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c race -f $MCM_DIR/test_hatsr.als
echo "Expected Output: SAT (race found)"
echo ""

echo "Running test_hatsnr.als..."
java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c no_race -f $MCM_DIR/test_hatsnr.als
echo "Expected Output: UNSAT (no race found)"
echo ""

java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c forbidden1 -f $MCM_DIR/test_hatsnr.als
echo "Expected Output: UNSAT (outcome impossible)"
echo ""

java $JAVA_FLAGS -jar $MCM_DIR/org.alloytools.alloy.dist.jar exec -c forbidden2 -f $MCM_DIR/test_hatsnr.als
echo "Expected Output: UNSAT (outcome impossible)"
echo ""
