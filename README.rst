pywbemtools: Python tools for communicating with WBEM servers
=============================================================

.. image:: https://img.shields.io/pypi/v/pywbemtools.svg
    :target: https://pypi.python.org/pypi/pywbemtools/
    :alt: Version on Pypi

.. image:: https://travis-ci.org/pywbem/pywbemtools.svg?branch=master
    :target: https://travis-ci.org/pywbem/pywbemtools
    :alt: Travis test status (master)

.. image:: https://ci.appveyor.com/api/projects/status/i022iaeu3dao8j5x/branch/master?svg=true
    :target: https://ci.appveyor.com/project/andy-maier/pywbemtools
    :alt: Appveyor test status (master)

.. image:: https://readthedocs.org/projects/pywbem/badge/?version=latest
    :target: https://pywbemtools.readthedocs.io/en/latest/
    :alt: Docs build status (master)

.. image:: https://img.shields.io/coveralls/pywbem/pywbem.svg
    :target: https://coveralls.io/r/pywbem/pywbemtools
    :alt: Test coverage (master)

.. image:: https://img.shields.io/pypi/pyversions/pywbemtools.svg?color=brightgreen
    :alt: PyPI - Python Version


Overview
--------

Pywbemtools is a collection of command line tools that communicate with WBEM
servers. The tools are written in pure Python and support Python 2 and Python
3.

At this point, pywbemtools includes a single command line tool named
``pywbemcli`` that uses the `pywbem package on Pypi`_ to issue operations to a
WBEM server using the `CIM/WBEM standards`_ defined by the `DMTF`_ to perform
system management tasks.

CIM/WBEM standards are used for a wide variety of systems management tasks
in the industry including DMTF management standards and the `SNIA`_
Storage Management Initiative Specification (`SMI-S`_).

Pywbemcli provides access to WBEM servers from the command line.
It provides functionality to:

* Explore the CIM data of WBEM servers. It can manage/inspect the CIM model
  components including CIM classes, CIM instances, and CIM qualifiers and
  execute CIM methods and queries on the WBEM server.

* Execute specific CIM-XML operations on the WBEM server as defined in `DMTF`_
  standard `DSP0200 (CIM Operations over HTTP)`_.

* Inspect and manage WBEM server functionality including:

  * CIM namespaces
  * Advertised WBEM management profiles
  * WBEM server brand and version information

* Capture detailed information on CIM-XML interactions with the WBEM server
  including time statistics and details of data flow.

* Maintain a file with persisted WBEM connection definitions so that pywbemcli
  can access multiple WBEM servers by name.

* Provide both a command line mode and an interactive mode where multiple
  pywbemcli commands can be executed within the context of a WBEM server.

* Use an integrated mock WBEM server to try out commands. The mock server
  can be loaded with CIM objects defined in MOF files or via Python scripts.


Installation
------------

Requirements:

1. Python 2.7, 3.4 and higher

2. Operating Systems: Linux, OS-X, native Windows, UNIX-like environments on
   Windows (e.g. Cygwin)

3. When using a pywbem version before 1.0.0 on Python 2, the following
   OS-level packages are needed:

   * On native Windows:

     - ``choco`` - Chocolatey package manager. The pywbemtools package installation
       uses Chocolatey to install OS-level software. See https://chocolatey.org/
       for the installation instructions for Chocolatey.

     - ``wget`` - Download tool. Can be installed with: ``choco install wget``.

   * On Linux, OS-X, UNIX-like environments on Windows (e.g. Cygwin):

     - ``wget`` - Download tool. Can be installed using the OS-level package
       manager for the platform.

Installation:

* When using a pywbem version before 1.0.0 on Python 2, install OS-level
  packages needed by the pywbem package:

  - On native Windows:

    .. code-block:: bash

        > wget -q https://raw.githubusercontent.com/pywbem/pywbem/master/pywbem_os_setup.bat
        > pywbem_os_setup.bat

  - On Linux, OS-X, UNIX-like environments on Windows (e.g. Cygwin):

    .. code-block:: bash

        $ wget -q https://raw.githubusercontent.com/pywbem/pywbem/master/pywbem_os_setup.sh
        $ chmod 755 pywbem_os_setup.sh
        $ ./pywbem_os_setup.sh

    The ``pywbem_os_setup.sh`` script uses sudo internally, so your userid
    needs to have sudo permission.

* Install the pywbemtools Python package:

  .. code-block:: bash

      > pip install pywbemtools

For more details, including how to install the needed OS-level packages
manually, see `pywbemtools installation`_.


Documentation and change history
--------------------------------

For the latest version released on Pypi:

* `Pywbemtools documentation`_
* `Pywbemtools change history`_


Quickstart
----------

All commands within pywbemcli show help with the ``-help`` or ``-h`` options:

.. code-block:: text

    $ pywbemcli --help
    . . .
    $ pywbemcli connection --help
    . . .
    $ pywbemcli connection add --help
    . . .

The following examples build on each other and show a typical sequence of
exploration of a WBEM server. For simplicity, they all operate against the
default namespace of the server, and use a persistent connection definition for
the server:

* Add a persistent connection definition named ``conn1`` for the WBEM server to
  be used, so that the subsequent commands can refer to it:

  .. code-block:: text

      $ pywbemcli connection add -s https://localhost -N -u user -p password -n conn1

* List the persistent connection definitions:

  .. code-block:: text

      $ pywbemcli connection list
      WBEM server connections:
      +--------+-------------------+-------------+--------+-----------+-------------+----------------------------------------+
      | name   | server            | namespace   | user   |   timeout | no-verify   | mock-server                            |
      |--------+-------------------+-------------+--------+-----------+-------------+----------------------------------------|
      | conn1  | https://localhost | root/cimv2  | user   |        30 | True        |                                        |
      +--------+-------------------+-------------+--------+-----------+-------------+----------------------------------------+

* Show the class tree, using the previously added connection definition ``conn1``:

  .. code-block:: text

      $ pywbemcli -n conn1 class tree
      root
       +-- TST_Lineage
       +-- TST_Person
       |   +-- TST_Personsub
       +-- TST_FamilyCollection
       +-- TST_MemberOfFamilyCollection

* Retrieve a single class from that class tree:

  .. code-block:: text

      $ pywbemcli -n conn1 class get TST_Person
      class TST_Person {

            [Key ( true ),
             Description ( "This is key prop" )]
         string name;

         string extraProperty = "defaultvalue";

      };

* Enumerate the instances of that class, returning only their instance names
  by use of the ``--no`` option:

  .. code-block:: text

      $ pywbemcli -n conn1 instance enumerate TST_Person --no
      root/cimv2:TST_Person.name="Gabi"
      root/cimv2:TST_Person.name="Mike"
      root/cimv2:TST_Person.name="Saara"
      root/cimv2:TST_Person.name="Sofi"
      root/cimv2:TST_PersonSub.name="Gabisub"
      root/cimv2:TST_PersonSub.name="Mikesub"
      root/cimv2:TST_PersonSub.name="Saarasub"
      root/cimv2:TST_PersonSub.name="Sofisub"

* Retrieve a single instance using one of these instance names:

  .. code-block:: text

      $ pywbemcli -n conn1 instance get 'root/cimv2:TST_Person.name="Sofi"'
      instance of TST_Person {
         name = "Sofi";
      };

* The instance to be retrieved can also be selected interactively by use of
  the wildcard instance key ("CLASSNAME.?"):

  .. code-block:: text

      $ pywbemcli -n conn1 instance get TST_Person.?
      Pick Instance name to process
      0: root/cimv2:TST_Person.name="Mike"
      1: root/cimv2:TST_Person.name="Saara"
      2: root/cimv2:TST_Person.name="Sofi"
      3: root/cimv2:TST_Person.name="Gabi"
      4: root/cimv2:TST_PersonSub.name="Mikesub"
      5: root/cimv2:TST_PersonSub.name="Saarasub"
      6: root/cimv2:TST_PersonSub.name="Sofisub"
      7: root/cimv2:TST_PersonSub.name="Gabisub"
      Input integer between 0 and 7 or Ctrl-C to exit selection: : 3
      instance of TST_Person {
         name = "Gabi";
      };

* There are multiple output formats supported. The enumerated instances can for
  example be formatted as a table of properties by use of the ``-o table``
  general option (these instances have only one property 'name'):

  .. code-block:: text

      $ pywbemcli -n conn1 -o table instance enumerate TST_Person
      Instances: TST_Person
      +------------+
      | name       |
      |------------|
      | "Gabi"     |
      | "Mike"     |
      | "Saara"    |
      | "Sofi"     |
      | "Gabisub"  |
      | "Mikesub"  |
      | "Saarasub" |
      | "Sofisub"  |
      +------------+

* Traverse all associations starting from a specific instance that is selected
  interactively:

  .. code-block:: text

      $ pywbemcli -n conn1 -o table instance associators TST_Person.?
      Pick Instance name to process
      0: root/cimv2:TST_Person.name="Mike"
      1: root/cimv2:TST_Person.name="Saara"
      2: root/cimv2:TST_Person.name="Sofi"
      3: root/cimv2:TST_Person.name="Gabi"
      4: root/cimv2:TST_PersonSub.name="Mikesub"
      5: root/cimv2:TST_PersonSub.name="Saarasub"
      6: root/cimv2:TST_PersonSub.name="Sofisub"
      7: root/cimv2:TST_PersonSub.name="Gabisub"
      Input integer between 0 and 7 or Ctrl-C to exit selection: : 0
      Instances: TST_FamilyCollection
      +-----------+
      | name      |
      |-----------|
      | "Family2" |
      | "Gabi"    |
      | "Sofi"    |
      +-----------+

Other operations against WBEM servers include getting information on namespaces,
the Interop namespace, WBEM server brand information, or the advertised
management profiles:

* Show the Interop namespace of the server:

  .. code-block:: text

      $ pywbemcli -n conn1 server interop
      Server Interop Namespace:
      Namespace Name
      ----------------
      root/PG_InterOp

* List the advertised management profiles:

  .. code-block:: text

      $ pywbemcli -n conn1 server profiles --organization DMTF
      Advertised management profiles:
      +----------------+----------------------+-----------+
      | Organization   | Registered Name      | Version   |
      |----------------+----------------------+-----------|
      | DMTF           | CPU                  | 1.0.0     |
      | DMTF           | Computer System      | 1.0.0     |
      | DMTF           | Ethernet Port        | 1.0.0     |
      | DMTF           | Fan                  | 1.0.0     |
      | DMTF           | Indications          | 1.1.0     |
      | DMTF           | Profile Registration | 1.0.0     |
      +----------------+----------------------+-----------+

Pywbemcli can also be executed in the interactive (REPL) mode by executing it
without entering a command or by using the command ``repl``. In this mode
the command line prompt is ``pywbemcli>``, the WBEM server connection is
maintained between commands and the general options apply to all commands
executed:

.. code-block:: text

    $ pywbemcli -n conn1
    Enter 'help' for help, <CTRL-D> or ':q' to exit pywbemcli.
    pywbemcli> server brand

    Server Brand:
    WBEM Server Brand
    -------------------
    OpenPegasus
    pywbemcli> server interop

    Server Interop Namespace:
    Namespace Name
    ----------------
    root/PG_InterOp
    pywbemcli> :q


Project Planning
----------------

For each upcoming release, the bugs and feature requests that are planned to
be addressed in that release are listed in the `pywbemtools issue tracker`_
with an according milestone set that identifies the target release.
The due date on the milestone definition is the planned release date.
There is usually also an issue that sets out the major goals for an upcoming
release.


Contributing
------------

For information on how to contribute to this project, see
`pywbemtools contributions`_.


License
-------

The pywbemtools package is licensed under the `Apache 2.0 License`_.


.. _pywbemtools documentation: https://pywbemtools.readthedocs.io/en/stable/
.. _pywbemtools installation: https://pywbemtools.readthedocs.io/en/stable/introduction.html#installation
.. _pywbemtools contributions: https://pywbemtools.readthedocs.io/en/stable/development.html#contributing
.. _pywbemtools change history: https://pywbemtools.readthedocs.io/en/stable/changes.html
.. _pywbemtools issue tracker: https://github.com/pywbem/pywbemtools/issues
.. _pywbem package on Pypi: https://pypi.org/project/pywbem/
.. _DMTF: https://www.dmtf.org/
.. _CIM/WBEM standards: https://www.dmtf.org/standards/wbem/
.. _DSP0200 (CIM Operations over HTTP): https://www.dmtf.org/sites/default/files/standards/documents/DSP0200_1.4.0.pdf
.. _SNIA: https://www.snia.org/
.. _SMI-S: https://www.snia.org/forums/smi/tech_programs/smis_home
.. _Apache 2.0 License: https://github.com/pywbem/pywbemtools/tree/master/LICENSE.txt
