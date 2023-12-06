import os
import click
import cv2
import numpy as np
from officialeye.utils import find_template


class TemplateFeature:
    def __init__(self, feature_dict: dict, template, /):
        self._template = template
        self.is_pattern = False if "pattern" not in feature_dict else bool(feature_dict["pattern"])
        self.id = str(feature_dict["id"])
        self.x = int(feature_dict["x"])
        self.y = int(feature_dict["y"])
        self.w = int(feature_dict["w"])
        self.h = int(feature_dict["h"])

    def draw(self, img):
        rect_color = (0, 0, 0xff) if not self.is_pattern else (0xff, 0, 0)
        label_color = (0, 0, 0xff)
        img = cv2.rectangle(img, (self.x, self.y), (self.x + self.w, self.y + self.h), rect_color, 4)
        label_origin = (self.x + 10, self.y + 30)
        img = cv2.putText(img, self.id, label_origin, cv2.FONT_HERSHEY_SIMPLEX, 1, label_color, 2, cv2.LINE_AA)
        return img

    def to_image(self):
        img = self._template.load_source_image()
        return img[self.y:self.y + self.h, self.x:self.x + self.w]

    def find_on_image(self, img):
        return find_template(img, self.to_image())


class Template:
    def __init__(self, yaml_dict: dict, path_to_template: str, /):
        self._path_to_template = path_to_template
        self.name = yaml_dict["name"]
        self._source = yaml_dict["source"]
        self.height, self.width, _ = self.load_source_image().shape
        self._features = [
            TemplateFeature(f, self) for f in yaml_dict["features"]
        ]

    def _get_source_image_path(self) -> str:
        path_to_template_dir = os.path.dirname(self._path_to_template)
        path = os.path.join(path_to_template_dir, self._source)
        return os.path.normpath(path)

    def load_source_image(self):
        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def _show(self, img):
        for feature in self._features:
            img = feature.draw(img)
        return img

    def show(self):
        img = self.load_source_image()
        img = self._show(img)
        output_path = "debug.png"
        cv2.imwrite(output_path, img)
        click.secho(f"Success. Exported '{output_path}'.", bg="green", bold=True)

    def apply(self, target, /):
        # find all patterns in the target image
        img = target.copy()

        source_points = []
        destination_points = []

        for f in self._features:
            if not f.is_pattern:
                continue
            score, (x, y) = f.find_on_image(target)

            source_points.append([x, y])
            source_points.append([x + f.w, y])
            source_points.append([x + f.w, y + f.h])
            source_points.append([x, y + f.h])

            destination_points.append([f.x, f.y])
            destination_points.append([f.x + f.w, f.y])
            destination_points.append([f.x + f.w, f.y + f.h])
            destination_points.append([f.x, f.y + f.h])

            img = cv2.rectangle(img, (x, y), (x + f.w, y + f.h), (0, 0, 0xff), 4)
            #for (x, y), color in zip(vertices, [(0, 0, 0xff), (0, 0xff, 0), (0xff, 0, 0), (0, 0xff, 0xff), (0xff, 0xff, 0), (0xff, 0, 0xff), (0xff, 0xff, 0xff)]):
            #    img = cv2.rectangle(img, (x, y), (x + w, y + h), color, 4)

        output_path = "debug.png"
        cv2.imwrite(output_path, img)
        click.secho(f"Pattern-matching success. Exported '{output_path}'.", bg="green", bold=True)

        click.echo(f"Source points: {source_points}")
        click.echo(f"Destination points: {destination_points}")

        homography = cv2.getPerspectiveTransform(np.float32(source_points), np.float32(destination_points))
        target_transformed = cv2.warpPerspective(target, np.float32(homography), (self.width, self.height), flags=cv2.INTER_LINEAR)
        target_transformed = self._show(target_transformed)

        output_path = "transformed.png"
        cv2.imwrite(output_path, target_transformed)
        click.secho(f"Success. Exported '{output_path}'.", bg="green", bold=True)

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._features)} features)"
