"""Entry point: python -m pysim8.kernel."""

from ipykernel.kernelapp import IPKernelApp

from ._kernel import Sim8Kernel

IPKernelApp.launch_instance(kernel_class=Sim8Kernel)
