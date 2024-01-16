---
icon: octicons/info-16
---

<figure markdown>
![OfficialEye logo](assets/img/logo/logo_bg_light.svg#only-light)
![OfficialEye logo](assets/img/logo/logo_bg_dark.svg#only-dark)
</figure>

# Introduction

OfficialEye is an advanced tool designed to extract information from flat documents, such as passports or application forms, through image analysis. Leveraging state-of-the-art symbolic AI techniques, OfficialEye empowers users to effortlessly transform raw images into standardized canonical forms, facilitating the seamless extraction and processing of crucial information.

![GitHub Release](https://img.shields.io/github/v/release/ZeroBone/OfficialEye?label=latest%20release)
![PyPI - Version](https://img.shields.io/pypi/v/officialeye)


## Key features

<div class="grid cards" markdown>

-   :material-clock-fast:{ .lg .middle } __Example-driven and user-friendly__

    ---

    OfficialEye boasts an intuitive and example-driven approach. As a user, all you need to do is provide an image of a sample document and articulate which parts contain information you are interested in, and which can be used to recognize similar documents. The tool automatically generalizes from your example, making it a user-friendly solution for various document recognition tasks.

-   :material-camera-document:{ .lg .middle } __Powerful template system__

    ---

    Templates encapsulate the nuances of document analysis and processing. Multiple document types are effortlessly managed by employing distinct templates, each configurable through a potent YAML-based scripting language. It allows you to express the contents of your documents comprehensively yet concisely, ensuring maintainability even for complex documents with numerous entries.

-   :material-code-block-braces:{ .lg .middle } __Highly modular and customizable__

    ---

    OfficialEye prioritizes modularity and customization. Each step of the image analysis process is separated and explained. The template scripting language allows users to switch between implementations of every component on-the-fly, without the need for recompilation. Inject custom implementations easily, tailoring the tool to your specific needs.

-   :material-brain:{ .lg .middle } __Consistency-driven detection__

    ---
    
    Out-of-the box, OfficialEye's supports an innovative consistency-driven detection approach, finely tuned for flat documents. Imagine the human ability to detect formatted documents at a glance: with an innate understanding of how a document appears, our brains effortlessly filters out incongruent elements. OfficialEye mirrors this by operating under the assumption that the document in the image is a flat surface and leveraging this inherent knowledge to significantly enhance the accuracy of the results.

-   :material-lightbulb-on:{ .lg .middle } __Visualizations__

    ---

    OfficialEye offers a debugging mode wherein integrated algorithms generate graphical visualizations, providing users with a transparent view of the tool's internal processes. In case of issues, these visualizations serve as a diagnostic aid, swiftly pinpointing areas for improvement and thus enhancing your document analysis experience.

- :material-scale-balance:{ .lg .middle } __Free and open source__

    ---

    Say goodbye to proprietary alternatives. OfficialEye is committed to the principles of freedom and transparency. Released under the GNU GPL-3.0 license, it provides a [free and open-source](https://en.wikipedia.org/wiki/Free_and_open-source_software) alternative, ensuring accessibility for all users.

    [:octicons-arrow-right-24: License](usage/other/license.md)

</div>

Whether you're a developer, data scientist, or enthusiast, OfficialEye is your go-to solution for accurate and efficient flat document analysis. Experience the future of document analysis with OfficialEye!

[Examples](usage/examples.md){ .md-button .md-button--primary} [Getting started](usage/getting-started/setup.md){ .md-button }