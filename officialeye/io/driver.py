from abc import ABC


class IODriver(ABC):

    def __init__(self, driver_id: str):
        self.__driver_id = driver_id
