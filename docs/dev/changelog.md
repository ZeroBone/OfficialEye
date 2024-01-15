# Changelog

## Release v1.1.0 (beta)

This release features a new mutation and interpretation system, and a feature class system.

* Huge refactor of the entire codebase, and numerous architecture improvements.
* Removed the `officialeye analyze` command, replacing its functionality with `officialeye test` and `officialeye run`.
* Simplified the implementation of IO Drivers, and removed the possibility of manually speficying the desired IO driver via the `--io` option, as it is no longer required.
* Implemented the feature class system, that allows grouping of features together in a non-verbose and meaningful way, and which, among other features, supports abstraction and inheritance.
* Removed the possibility of attaching meta values to features, as this has been a bad design choice.
* Implemented the feature interpretation system, allowing one to specify for every individual feature the way in which it is to be intepreted.
* Implemented the mutation system and the ability of adding mutators to feature classes, that get applied before executing the interpretation system.
* The score value is now included into the output of the `officialeye run` command. This value represents the level of confidence in the correctness of the result.
* Fixed incorrect behaviour when a template keypoint required matches, but there were actually no matches whatsoever.
* Added `--show-features` options to the `officialeye test` command, that allows one to specify whether the feature borders are to be visualized or not.
* Added `--hide-features` and `--hide-keypoints` options to the `officialeye show` command.
* Added the possibility of applying mutators to the template image and to the target images.
* Added grayscaling, denoising, and contrast increase mutators.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.0){ .md-button }

## Pre-Release v1.0.2 (beta)

This pre-release features automatic template config generation, engine-specific configurations, performance improvements, and more!

* Automatic template configuration file generation via the `officialeye create` command (see #2).
* Improved logging.
* Minor bug fixes.
* Improved the `officialeye show` command, made in particular the overlay look better.
* The matching system now supports engine-specific configuration. For example, if you are using the `sift_flann` keypoint matcher, you can now specify the `sensitivity` value in the `matching.config.sift_flann.sensitivity` option of the template configuration file.
* Improved error handling.
* Significantly improved the performance of the `sift_flann` keypoint matching engine.
* Template features can now have fully customizable meta information attached to them. This allows more flexibility for concrete supervision engine implementations.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.2){ .md-button }

## Pre-Release v1.0.1 (beta)

This pre-release features new and improved Supervision Engines, Error Handling, IO Drivers, OCR Support, and more.

* Implemented three supervision engines - `combinatorial`, `least_squares_regression`, and `orthogonal_regression`. The combinatorial supervision engine used to rely on Cylindrical Algebraic Decomposition; now it relies on the z3 `QF_LRA` optimization engine.
* The supervision engines are now completely separated from the matching engines: Thus, they can be combined in any way.
* Added support for analyzing an image against multiple templates: the result with the highest score gets chosen as the final result at the end: the scoring system is completely customizable via a flexible API
* New logging system with colored messages.
* Completely rewritten the error handling system - now it is based on python exceptions and is much more reliable and less error-prone.
* Abstracted out the handling of input/output. Now it is possible to easily integrate any custom handling of any of the system's output, by implementing and IO driver.
* Added a new tesseract-based OCR IO Driver.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.1){ .md-button }

## Pre-Release v1.0.0 (beta)

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.0){ .md-button }