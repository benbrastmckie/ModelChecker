"""Setup file for the ModelChecker package.

This file is used to install the package in development mode,
which is especially useful when working on NixOS or other
environments where you can't easily use pip.

Usage:
    # Install in development mode
    python setup.py develop
    
    # Run tests
    pytest
"""

from setuptools import setup, find_packages

# Load the version from pyproject.toml (manually to avoid dependencies)
version = "0.8.25"  # Default version
try:
    with open("pyproject.toml", "r") as f:
        for line in f:
            if line.strip().startswith("version ="):
                version = line.split("=")[1].strip().strip('"').strip("'")
                break
except FileNotFoundError:
    pass

setup(
    name="model-checker",
    version=version,
    description="A hyperintensional theorem prover for modal, counterfactual conditional, constitutive explanatory, and extensional operators.",
    author="Benjamin Brast-McKie",
    author_email="benbrastmckie@gmail.com",
    url="https://github.com/benbrastmckie/ModelChecker",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    install_requires=[
        "z3-solver",
    ],
    python_requires=">=3.8",
    entry_points={
        "console_scripts": [
            "model-checker=model_checker.__main__:run",
        ],
    },
    classifiers=[
        "Programming Language :: Python :: 3.8",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
)