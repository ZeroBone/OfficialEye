from setuptools import setup

setup(
    name="officialeye",
    version="1.0.0",
    py_modules=["officialeye"],
    install_requires=["click", "pyyaml", "strictyaml", "opencv-contrib-python-headless", "numpy", "opencv-contrib-python-headless", "z3-solver"],
    entry_points={
        "console_scripts": [
            "officialeye = officialeye.officialeye:cli"
        ]
    }
)
