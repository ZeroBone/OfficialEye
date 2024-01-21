import os

from officialeye._internal.error.errors.io import ErrIOInvalidPath
from officialeye._internal.logger.singleton import get_logger


def create_example_template_config_file(template_path: str, template_image: str, template_id: str, template_name: str, force_mode: bool, /):

    # validate the path first
    if os.path.isdir(template_path):
        raise ErrIOInvalidPath(
            f"while making sure that '{template_path}' references a file",
            f"This path references a directory."
        )

    # determine source config value
    if os.path.isabs(template_image):
        # if the path to the specified template source file is absolute,
        # then we simply put the same absolute path in the template config
        template_source_config = template_image
    else:
        # otherwise, the path is relative to the working directory the program was started in
        # however, we are interested in the path to the template image relative to the template configuration file
        # therefore, we 'subtract' from the template_image path the template_path path
        template_source_config = os.path.relpath(template_image, os.path.dirname(template_path))

    if os.path.exists(template_path) and not force_mode:
        raise ErrIOInvalidPath(
            f"while making sure that path '{template_path}' exists",
            f"There is already a file at this path. Use --force to suppress this error."
        )

    dir_name = os.path.dirname(template_path)
    if dir_name != "" and dir_name != "/" and not os.path.exists(dir_name):
        if force_mode:
            os.makedirs(dir_name, exist_ok=True)
        else:
            raise ErrIOInvalidPath(
                f"while making sure that path '{template_path}' exists",
                f"Not all directories leading to the file exist. Use --force to create the missing directories."
            )

    template_yml = f'''# This is the ID of the template. It is needed to identify this template in the API and must be alphanumeric and unique.
id: "{template_id}"

# The name of the template, as should be displayed to the user
name: "{template_name}"

# This is the path to the example document you want to use as a base for the template.
# The path can be absolute or relative. If it is relative, then it will be resolved relative to the location of the current file.
source: "{template_source_config}"
# A mutator is a size-preserving image transforming function. Examples of mutators include noise reduction and color correction. 
mutators:
  # A list of mutators that should be applied to the above template source image before the unification phase
  source:
  # A list of mutators that should be applied to the input image before the unification phase
  target:

# A list of keypoints located in the template source image specified above.
# A keypoint is a rectangular region that should be present in all documents of this kind, and that
# should be used to find correspondences between the position of the given image and the positions in the template source image.
keypoints:
  # Example keypoint specification.
  # Remember to remove or customize this keypoint that is here only for demonstration purposes.
  example_keypoint_name:
    # Remember that the origin is located at the top left corner of the image. In other words,
    # the x-axis points to the right, and the y-axis points down (not up!).
    x: 10 # the x-coordinate of the top left corner of the rectangle (measured in pixels).
    y: 10 # the y-coordinate of the top left corner of the rectangle (measured in pixels).
    w: 100 # width of the rectangle (measured in pixels)
    h: 50 # height of the rectangle (measured in pixels)
    matches:
      # Minimum amount of matches that should be identified within this keypoint's region when analyzing an image.
      min: 0
      # Maximum amount of matches that should be identified within this keypoint's region when analyzing an image.
      max: 40

# Matching configuration
# Matching is the process of finding equal patterns in the given image and the template source image,
# thus establishing correspondences between positions.
# Although better matchings will of course contribute to the accuracy of the document analysis, it is
# completely fine for a matching algorithm to err in some cases.
matching:
  # Here you can specify the name of the matching engine that should be used to find correspondences between
  # positions of the given image and those of the template source image provided above.
  # Available engines: sift_flann
  engine: sift_flann
  # Engine-specific configuration
  config:
    # Configuration specific to the `sift_flann` matching engine.
    sift_flann:
      sensitivity: 0.7

# Supervision configuration
# Supervision is the process of unifying the given document image with the template source,
# based on the (partially unreliable) information received from the matching algorithm
supervision:
  # Here you can specify the name of the supervision engine that should be used to find correspondences between
  # positions of the given image and those of the template source image provided above.
  # Available engines: orthogonal_regression, least_squares_regression, combinatorial
  engine: combinatorial
  # Engine-specific configuration
  config:
    # Here you can specify engine-specific configurations
    combinatorial:
      # A coefficient between 0 and 1, representing the fraction of matches that should be chosen as the basis for inferring the way the document
      # is positioned in the image provided. The larger the coefficient, the more reliable the supervision result will be.
      # However, increasing this value will also increase the risk of wrongfully not detecting a document at all.
      # If your matching engine produces a lot of false positives, it is recommended to keep this value low, and vice versa.
      min_match_factor: 0.1
      # The combinatorial engine uses an affine linear transformation model to represent the way the document is located in the image provided.
      # It then chooses at least `min_match_factor` * (total amount of matches) matches that cause the data to fit the model, up to the error
      # specified here, measured in pixels along one of the axis. Thus, the lower this value is, the higher will be the quality of the
      # combinatorial supervision engine's output. On the other hand, a very small value will increase
      # the risk of wrongfully not detecting a document at all.
      # Recommended value: between 2 and 10 pixels
      max_transformation_error: 5

  # Since the supervision engine may produce multiple results.
  # This option allows you to specify the strategy that should be used to choose a final result.
  # Available strategies: first, best_mse, best_score
  # The `first` strategy simply returns the first result produced
  # The `random` strategy chooses a random result produced
  # The `best_mse` strategy finds the result which has the lowest mean squared error when translating template points to target points
  # The `best_score` strategy returns the result with the highest score (what `score` represents depends on the supervision engine)
  result: best_score

# A list of features located in the template source image specified above.
# A feature is a rectangular region containing any information of interest, such as text.
# In other words, the corresponding regions in the target image will be found during document analysis.
features:
  # Example feature specification.
  # Remember to remove or customize this feature that is here only for demonstration purposes.
  # Remember that the origin is located at the top left corner of the image. In other words,
  # the x-axis points to the right, and the y-axis points down (not up!).
  example_feature_name:
    # Remember that the origin is located at the top left corner of the image. In other words,
    # the x-axis points to the right, and the y-axis points down (not up!).
    x: 110 # the x-coordinate of the top left corner of the rectangle (measured in pixels)
    y: 10 # the y-coordinate of the top left corner of the rectangle (measured in pixels)
    w: 100 # width of the rectangle (measured in pixels)
    h: 10 # height of the rectangle (measured in pixels)
    class: example_feature_class # optional, the class of this feature (see below)

# A feature class can be used to group similar features together
# Feature classes are identified by a unique name, and can inherit other classes.
feature_classes:
  # For example, the following entry defines a feature class named example_feature_class
  example_feature_class:
    # An abstract class cannot be directly used by any concrete feature, but can be incomplete.
    # To use an abstract class, a non-abstract subclass has to be created.
    # A non-abstract class can be used by concrete features, but cannot be incomplete.
    abstract: no # Optional. By default, feature classes are not abstract.
    # A mutator is a method of transforming an image into another image.
    # Examples of mutators include image denoising, grayscale coloring, etc.
    # You can even define and use your own mutators.
    # In this example, we use a mutator that reduces image noise.
    mutators: # A sequence of mutators that should be applied to the region of a feature, before it is processed further.
      - id: non_local_means_denoising # Name of the mutator
        config: # Optional mutator-specific configuration
          colored: yes
    interpretation:
      # An interpretation method defines the way in which the mutated feature location should be processed further
      # For example, the ocr_tesseract method will apply the Tesseract OCR to the image.
      method: ocr_tesseract
      # Intepretation-engine-specific configuration values
      config:
        config: --dpi 10000 --oem 3 --psm 6
        lang: eng
    '''

    with open(template_path, "w") as fh:
        fh.write(template_yml)

    get_logger().info(f"Initialized template configuration file at '{template_path}'.")
