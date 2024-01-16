---
icon: material/file-document-edit
---

# YAML Basics

OfficialEye uses the YAML (`.yml`) format for all configuration files.

## What is YAML?

YAML is a data-serialization language that is both readable for humans and easily parseable by computers.

YAML is `key: "value"` based. This means you use a *key* to get a certain value. Values should be surrounded by double quotes (`"..."`).
This can be demonstrated using the following example.

```yaml title="YAML Data Format"
key: "value"
cat: "Some text data about the cat"
```

Now the key `cat` can be used to obtain `Some text data about the cat`.

Keys and values can also be nested into each other. Then they **must** be indented with two **spaces**.

```yaml title="Nested YAML"
outer_name:
  inner_name: "inner_value"
  another_key: "OfficialEye is great!"
```

Tabs are not supported. Use spaces instead.

## Further reading

For more information about the `YAML` format, we refer you to [this tutorial](https://spacelift.io/blog/yaml). Note that in fact, due to security and compatibility reasons, OfficialEye uses only a subset of `YAML` called [strictyaml](https://github.com/crdoconnor/strictyaml), meaning that not all YAML features are supported.