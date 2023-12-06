from setuptools import setup

setup(
    name="officialeye",
    version="1.0.0",
    py_modules=["officialeye"],
    install_requires=["click", "pyyaml", "opencv-contrib-python-headless", "numpy", "opencv-contrib-python-headless"],
    entry_points={
        "console_scripts": [
            "officialeye = officialeye.officialeye:cli"
        ]
    }
)