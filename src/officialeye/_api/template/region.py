class Region:

    def __init__(self, /, *, identifier: str, x: int, y: int, w: int, h: int):
        self.identifier = identifier
        self.x = x
        self.y = y
        self.w = w
        self.h = h


class Feature(Region):

    def __init__(self, /, **kwargs):
        super().__init__(**kwargs)


class Keypoint(Region):

    def __init__(self, /, *, matches_min: int, matches_max: int, **kwargs):
        super().__init__(**kwargs)

        self.matches_min = matches_min
        self.matches_max = matches_max
