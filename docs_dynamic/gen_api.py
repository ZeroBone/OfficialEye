"""Generate the API reference pages and navigation."""

from pathlib import Path

import mkdocs_gen_files


def snake_case_to_title(input_str: str, /) -> str:
    return " ".join([f"{word[0].upper()}{word[1:]}" for word in input_str.split("_") if len(word) > 0])


nav = mkdocs_gen_files.Nav()

src = Path(__file__).parent.parent / "src"

internal_module = src / "officialeye" / "_internal"
api_module = src / "officialeye" / "_api"

mod_symbol = '<code class="doc-symbol doc-symbol-nav doc-symbol-module"></code>'

for path in sorted(src.rglob("officialeye/**/*.py")):

    module_path = path.relative_to(src).with_suffix("")

    if internal_module in path.parents:
        # the current module is a submodule of the internal api
        doc_path = path.relative_to(internal_module).with_suffix(".md")
        full_doc_path = Path("dev", "api", doc_path)
    elif api_module in path.parents:
        # the current module is part of the public api
        doc_path = path.relative_to(api_module).with_suffix(".md")
        full_doc_path = Path("api", doc_path)
    else:
        continue

    parts = tuple(module_path.parts)

    if parts[-1] == "__init__":
        parts = parts[:-1]
        doc_path = doc_path.with_name("index.md")
        full_doc_path = full_doc_path.with_name("index.md")
    elif parts[-1] == "__main__":
        continue

    # nav_parts = [f"{mod_symbol} {part}" for part in parts]
    nav_parts = [snake_case_to_title(part) for part in parts]

    nav[tuple(nav_parts)] = doc_path.as_posix()

    with mkdocs_gen_files.open(full_doc_path, "w") as fd:
        ident = ".".join(parts)
        fd.write(f"::: {ident}")

    mkdocs_gen_files.set_edit_path(full_doc_path, path)
