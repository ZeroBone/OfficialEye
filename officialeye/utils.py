import typing
import numpy as np
import cv2

def _remove_noise(img):
    # blur
    blur = cv2.GaussianBlur(img, (0, 0), sigmaX=33, sigmaY=33)

    # divide
    divide = cv2.divide(img, blur, scale=255)

    # otsu threshold
    thresh = cv2.threshold(divide, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]

    # apply morphology
    kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (3, 3))
    morph = cv2.morphologyEx(thresh, cv2.MORPH_CLOSE, kernel)

    return morph


def find_template(img: cv2.Mat, template: cv2.Mat):
    # make the image and template grayscale
    img = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
    template = cv2.cvtColor(template, cv2.COLOR_RGB2GRAY)

    # remove noise from image and template
    img = _remove_noise(img)
    template = _remove_noise(template)
    # img = cv2.morphologyEx(img, cv2.MORPH_CLOSE, kernel, iterations=1)
    # template = cv2.morphologyEx(template, cv2.MORPH_CLOSE, kernel, iterations=1)

    cv2.imwrite("_d_img.png", img)
    cv2.imwrite("_d_template.png", template)

    """
    # perform actual template matching
    vertices = []

    for method in (cv2.TM_CCOEFF, cv2.TM_CCOEFF_NORMED, cv2.TM_CCORR, cv2.TM_CCORR_NORMED, cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED):
        result = cv2.matchTemplate(img, template, method)
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(result)
        if method in (cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED):
            top_left = min_loc
        else:
            top_left = max_loc
        vertices.append(top_left)

    return vertices
    """

    result = cv2.matchTemplate(img, template, cv2.TM_SQDIFF_NORMED)
    min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(result)
    return min_val, min_loc
