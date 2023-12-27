import cv2


def remove_noise(img):
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
