import click
import tempfile
# noinspection PyPackageRequirements
import cv2


def export_and_show_image(img):

    with tempfile.NamedTemporaryFile(prefix="officialeye_", suffix=".png", delete=True) as fp:
        cv2.imwrite(fp.name, img)
        click.secho(f"Success. Exported '{fp.name}'.", bg="green", bold=True)
        click.launch(fp.name, locate=False)
        click.pause()
        fp.close()
