class Match:

    def __init__(self, template_id: str, template_point, target_point, /):
        self.template_id = template_id
        self.template_point = template_point
        self.target_point = target_point

    def __str__(self) -> str:
        return "%s: (%4d, %4d) <-> (%4d, %4d)" % (self.template_id, self.template_point[0], self.template_point[1],
                                                  self.target_point[0], self.target_point[1])
