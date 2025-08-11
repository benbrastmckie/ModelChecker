#!/bin/bash
# Test modular iterator with relevance theory

echo "Testing modular iterator implementation..."
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py > modular_output.txt 2>&1

echo "Checking output..."
grep -E "(MODEL|REL_CM_1|Error|escape|NotImplementedError)" modular_output.txt | head -20

echo ""
echo "Model count:"
grep -c "MODEL " modular_output.txt

echo ""
echo "Has MODEL 2:"
grep -q "MODEL 2" modular_output.txt && echo "YES" || echo "NO"

echo ""
echo "Any errors:"
grep -E "(Error|Exception|NotImplementedError)" modular_output.txt | head -5