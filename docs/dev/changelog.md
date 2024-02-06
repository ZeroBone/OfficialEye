# Changelog

## Release 1.2.0 (beta)

### Major changes

* Implemented the OfficialEye API. Now it is possible to interact with the program programatically, without the need of running the CLI.
* Reimplemented the CLI as a layer on top of the new API. Thus, the API and the internal implementation no longer contain any code that is specific to the CLI user interface. In particular, it is now easy to implement different frontends that rely on OfficialEye as a backend service.
* Implemented a framework for transparent and process-safe interaction with the API backend.
* Switched from thread-based to process-based parallelism for resource-intensive backend operations.
* Substrantially improved the CLI user interface.
* Numerous other related architecture changes aimed at the long-term stability of the software.
* Integrated a new error handling system and related debugging facilitibes.

### Minor changes

* Removed the `--worker` argument from the `run` and `test` commands, because it has become redundant and unnececcary in light of the new architecture.
* Implemented a new approach to handling image outputting in the CLI, that is much more flexible compared to the previous one.
* Improved type annotations.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.2.0){ .md-button }

## Release 1.1.5 (beta)

* Added an `--interpret` option to the `run` and `test` commands, allowing one to optionally use a different target image for the interpretation phase.
* Set up linting and basic unit testing to ensure better code quality.
* Minor improvements and bug fixes.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.5){ .md-button }

## Release 1.1.4 (beta)

* Added a new `rotate` mutator, that rotates an image by a multiple of 90 degrees.
* Added a new `file` interpretation method that is similar to `file_temp`, but can save a file at the specified path.
* Improved the error handling system.
* Fixed multiple bugs, including one critical bug.
* Added a possibility of using external errors as causes of OfficialEye errors.
* Added support for non-shape-preserving mutators.
* Added a new `-re` flag allowing one to disable built-in error handling.
* Slightly changed logging style.
* Refactor.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.4){ .md-button }

## Release 1.1.3 (beta)

* The `tesseract_ocr` interpretation method no longer has default Tesseract OCR configuration values predefined.
* Added a new `file_temp` interpretation method that allows one to save features as temporary files.
* Separated debugging mode and step visualization mode. Now the two settings are independent of each other.
* Added a new flag `--visualize` to the `run` and `test` commands, allowing users to toggle visualization mode.
* Simplified the image exporting system.
* Removed the `--dedir` global argument. Users should now use `--edir` instead.
* Rewritten the context and context management system, making the API much closer to being stable.
* Other substrantial refactor.
* Other architecture improvements.
* Fixed numerous typos and inconsistencies in comments and strings.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.3){ .md-button }

## Release 1.1.2 (beta)

There are only minor improvements compared to the previous release (version 1.1.1). This release serves as an initial release for PyPI.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.2){ .md-button }

## Release 1.1.1 (beta)

* Fixed many minor bugs, typos and inconsistencies.
* Refactor.
* Many documentation improvements.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.1){ .md-button }

## Release 1.1.0 (beta)

This release features a new mutation and interpretation system, and a feature class system.

* Huge refactor of the entire codebase, and numerous architecture improvements.
* Removed the `officialeye analyze` command, replacing its functionality with `officialeye test` and `officialeye run`.
* Simplified the implementation of IO Drivers, and removed the possibility of manually speficying the desired IO driver via the `--io` option, as it is no longer required.
* Implemented the feature class system that allows grouping of features together in a non-verbose and meaningful way, and which, among other features, supports abstraction and inheritance.
* Removed the possibility of attaching meta values to features, as this has been a bad design choice.
* Implemented the feature interpretation system, allowing one to specify for every feature the way in which it is to be intepreted.
* Implemented the mutation system and the ability of adding mutators to feature classes that get applied before executing the interpretation system.
* The score value is now included in the output of the `officialeye run` command. This value represents the level of confidence in the correctness of the result.
* Fixed incorrect behavior when a template keypoint required matches, but there were actually no matches whatsoever.
* Added `--show-features` options to the `officialeye test` command, that allows one to specify whether the feature borders are to be visualized or not.
* Added `--hide-features` and `--hide-keypoints` options to the `officialeye show` command.
* Added the possibility of applying mutators to the template image and to the target images.
* Added grayscaling, denoising, and contrast increasing mutators.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.1.0){ .md-button }

## Pre-Release 1.0.2 (beta)

This pre-release features automatic template config generation, engine-specific configurations, performance improvements, and more!

* Automatic template configuration file generation via the `officialeye create` command (see #2).
* Improved logging.
* Minor bug fixes.
* Improved the `officialeye show` command, improved in particular the overlay look.
* The matching system now supports engine-specific configuration. For example, if you are using the `sift_flann` keypoint matcher, you can now specify the `sensitivity` value in the `matching.config.sift_flann.sensitivity` option of the template configuration file.
* Improved error handling.
* Significantly improved the performance of the `sift_flann` keypoint matching engine.
* Template features can now have fully customizable meta-information attached to them. This allows more flexibility for concrete supervision engine implementations.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.2){ .md-button }

## Pre-Release 1.0.1 (beta)

This pre-release features new and improved Supervision Engines, Error Handling, IO Drivers, OCR Support, and more.

* Implemented three supervision engines - `combinatorial`, `least_squares_regression`, and `orthogonal_regression`. The combinatorial supervision engine used to rely on Cylindrical Algebraic Decomposition; now it relies on the z3 `QF_LRA` optimization engine.
* The supervision engines are now completely separated from the matching engines: Thus, they can be combined in any way.
* Added support for analyzing an image against multiple templates: the result with the highest score gets chosen as the final result at the end: the scoring system is completely customizable via a flexible API
* New logging system with colored messages.
* Completely rewritten the error handling system—now it is based on python exceptions and is much more reliable and less error-prone.
* Abstracted out the handling of input/output. Now it is possible to easily integrate any custom handling of the system's output, by implementing an IO driver system.
* Added a new tesseract-based OCR IO Driver.

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.1){ .md-button }

## Pre-Release 1.0.0 (beta)

[View on GitHub](https://github.com/ZeroBone/OfficialEye/releases/tag/1.0.0){ .md-button }