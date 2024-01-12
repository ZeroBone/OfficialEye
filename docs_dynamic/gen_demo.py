"""Generates a usage example for the documentation"""
import os
import shutil
from pathlib import Path

import mkdocs_gen_files

demo_dir = Path(os.path.dirname(os.path.realpath(__file__))).parent / "demo"
docs_dir = Path(os.path.dirname(os.path.realpath(__file__))).parent / "docs"
docs_dynamic_dir = Path(os.path.dirname(os.path.realpath(__file__))).parent / "docs_dynamic"

docs_demo_img_dir = docs_dir / "assets" / "img" / "demo"

os.makedirs(docs_demo_img_dir, exist_ok=True)

shutil.copyfile(
    demo_dir / "input_images" / "driver_license_ru_01.jpg",
    docs_demo_img_dir / "driver_license_ru_01.jpg"
)

with open(docs_dynamic_dir / "usage" / "basics.md", "r", encoding="UTF-8") as input_fd:
    with mkdocs_gen_files.open(docs_dir / "usage" / "basics.md", "w") as output_fd:
        while line := input_fd.readline():
            line = line.rstrip()

            if not line.startswith("`{") or not line.endswith("}`"):
                print(line, file=output_fd)
                continue

            # this is a placeholder
            placeholder = line[2:-2]
            print(f"Found placeholder '{placeholder}'.")
