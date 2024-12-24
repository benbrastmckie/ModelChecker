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

# Run tests
pytest

# Run python3 -m build
python3 -m build

# Check if the build was successful
if [ $? -eq 0 ]; then
    # Run twine upload dist/*
    twine upload dist/*
else
    echo "Build failed. Aborting upload."
fi

