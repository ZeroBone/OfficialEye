<figure markdown>
![OfficialEye logo](assets/img/logo/logo_bg_light.svg#only-light)
![OfficialEye logo](assets/img/logo/logo_bg_dark.svg#only-dark)
</figure>

# Introduction

OfficialEye is a perfect solution if you need to reliably extract important information from a document (e.g. passport or certificate) based on its image. The tool relies on modern AI to transform the original image to a standartized canonical form, whereupon it processes the information you need.

<div class="grid cards" markdown>

-   :material-clock-fast:{ .lg .middle } __Example-driven and easy to use__

    ---

    OfficialEye is easy and intuitive to use because it is example-driven: as a user, all you need to do is:
    
    * Provide an image of an *example* document;
    * Explain, based on that example, how to recognize other documents of the same kind;

    Everything else is handled *automatically*! In particular, the tool will generalize your example to a way of processing arbitrary documents of that type.

-   :material-hammer-screwdriver:{ .lg .middle } __Powerful template system__

    ---

    Templates capture all aspects of how a certain kind of documents should be analyzed and processed. For multiple document types, you simply use multiple templates - the particular document type at hand will be detected automatically.

    Every template can be configured via a powerful `YAML`-based scripting language. It is designed to allow users to express contents of documents in a comprehensive and concise way that remains maintainable even if your document contains hundreds of entries.

-   :material-code-block-braces:{ .lg .middle } __Highly modular and customizable__

    ---

    All the steps during image analysis are clearly separated and explained.

    Via the template scripting language, you can easily change the implementation of every component without recompiling the project, or even inject custom implementations.

    [:octicons-arrow-right-24: TODO](#)

-   :material-scale-balance:{ .lg .middle } __Free and Open Source, GPL-3.0__

    ---

    Most if not all other comparable tools are either [proprietary](https://en.wikipedia.org/wiki/Proprietary_software) or are too generic and thus lack fine-grained optimization for the flat-surface document analysis model.

    By contrast, OfficialEye is [free and open source](https://en.wikipedia.org/wiki/Free_and_open-source_software), licensed under the GNU GPL-3.0 license.

    [:octicons-arrow-right-24: License](dev/license.md)

</div>

[:octicons-arrow-right-16: Getting started](./tutorials/getting-started/setup.md){ .md-button .md-button--primary}

## Example

Suppose we are interested in retreiving information about a person from a photo of their driver's license. Moreover, and as demonstrated in the following example, the image may well be of low quality, the document therein may be rotated, zoomed, held at an angle, etc.

???+ example "Input image"
    ![Driver license photo](./assets/img/demo/driver_license_ru_01.jpg){ loading=lazy }

To tackle the problem, we need a properly-positioned and high-quality image of an example document. For this demonstration, we will use the following scan of another driver's license, which we will hereinafter call *template image*.

???+ tip "Template image"
    ![Driver license photo](./assets/img/demo/driver_license_ru.jpg){ loading=lazy }

### Creating a template

Intuitively, now need to explain OfficialEye, which parts of this template image contain information we are interested in, and which features are present on any document of this kind and can thus be used to find and recognize the document in other images. Templates conveniently capture this information together with the template image. We shall now create a template called `Driver's License RU` with identifier `driver_license_ru`.

```shell
officialeye create demo/driver_license_ru/template.yml demo/driver_license_ru/template.jpg --name "Driver License RU" --id driver_license_ru
```

The `demo/driver_license_ru/template.jpg` path refers to the template image, while the above command creates a `YAML` template configuration file at path `demo/driver_license_ru/template.yml`. We now explain the relevant parts of this file.

```yaml title="demo/driver_license_ru/template.yml" hl_lines="5 6 7 8 9 10 11 12"
id: "driver_license_ru" # (1)!
name: "Driver License RU" # (2)!
source: "template.jpg" # (3)!
keypoints: # (4)!
  example_keypoint_name:
    x: 10
    y: 10
    w: 100
    h: 50
    matches:
      min: 0
      max: 40
features:
  example_feature_name:
    x: 110
    y: 10
    w: 100
    h: 10
    class: example_feature_class
feature_classes:
  example_feature_class:
    abstract: no
    mutators:
      - id: non_local_means_denoising
        config:
          colored: yes
    interpretation:
      method: ocr_tesseract
      config:
        config: --dpi 10000 --oem 3 --psm 6
        lang: eng
# ... other properties 
```

1. This is the ID of the template. It is needed to identify this template in the API and must be alphanumeric and unique.
2. The name of the template, as should be displayed to the user.
3. Path to the template image.
4. A list of keypoints located in the template source image specified above. A keypoint is a rectangular region that should be present in all documents of this kind, and that should be used to find correspondences between the position of the given image and the positions in the template source image.

!!! info "Not familiar with the above syntax?"
    Above we have used `YAML` syntax. If you are not familiar with it, read [this page](./tutorials/getting-started/yaml-basics.md). 