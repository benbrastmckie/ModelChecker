# run with: bash update.sh
# this script updates the package on PyPI given appropriate permissions

# Increase the patch number in pyproject.toml
current_version=$(grep -Po '(?<=version = ")[^"]*' pyproject.toml)
new_version=$(echo $current_version | awk -F. -v OFS='.' '{$NF=$NF+1; print $0}')
sed -i "s/version = \"$current_version\"/version = \"$new_version\"/" pyproject.toml

# Increase the patch number in __init__.py
sed -i "s/__version__ = \"$current_version\"/__version__ = \"$new_version\"/" src/model_checker/__init__.py

# Delete the dist directory and model_checker.egg-info directory
rm -rf dist 
rm -rf src/model_checker.egg-info

# Run tests for specific theory directories
theory_dirs=("default" "exclusion" "imposition") # "bimodal" 
failed_dirs=()

echo "Running tests for specific theory directories..."
for dir in "${theory_dirs[@]}"; do
    echo "Testing theory_lib/$dir..."
    if ! pytest "src/model_checker/theory_lib/$dir"; then
        echo "Tests failed for theory_lib/$dir"
        failed_dirs+=("$dir")
    fi
done

if [ ${#failed_dirs[@]} -gt 0 ]; then
    echo -e "\nTests failed in the following directories:"
    printf '%s\n' "${failed_dirs[@]}"
    
    read -p "Do you want to continue with build and upload anyway? (y/N) " response
    if [[ ! "$response" =~ ^[Yy]$ ]]; then
        echo "Aborting build and upload."
        exit 1
    fi
    echo "Continuing with build and upload despite test failures..."
fi

# Run python3 -m build
python3 -m build

# Check if the build was successful
if [ $? -eq 0 ]; then
    # Run twine upload dist/*
    twine upload dist/*
else
    echo "Build failed. Aborting upload."
fi

