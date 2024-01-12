# Changelog

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

## Pre-Release v1.0.1 (beta)

This pre-release features new and improved Supervision Engines, Error Handling, IO Drivers, OCR Support, and more.

* Implemented three supervision engines - `combinatorial`, `least_squares_regression`, and `orthogonal_regression`. The combinatorial supervision engine used to rely on Cylindrical Algebraic Decomposition; now it relies on the z3 `QF_LRA` optimization engine.
* The supervision engines are now completely separated from the matching engines: Thus, they can be combined in any way.
* Added support for analyzing an image against multiple templates: the result with the highest score gets chosen as the final result at the end: the scoring system is completely customizable via a flexible API
* New logging system with colored messages.
* Completely rewritten the error handling system - now it is based on python exceptions and is much more reliable and less error-prone.
* Abstracted out the handling of input/output. Now it is possible to easily integrate any custom handling of any of the system's output, by implementing and IO driver.
* Added a new tesseract-based OCR IO Driver.

## Pre-Release v1.0.0 (beta)

Initial release. 