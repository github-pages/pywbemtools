# (C) Copyright 2019 IBM Corp.
# (C) Copyright 2019 Inova Development Inc.
# All Rights Reserved
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""
Class to represent the concept and implementation of an association shrub.

A shrub is a view of association relations that gathers and presents all of the
information about a relation. I differs from the associator and reference
commands in that they present the user with just a set of CIM objects or
their names, and not a view of the relations between the components that
make up a CIM association.

It is based on the parameters of the pywbem associators operation.

It builds the information by using the reference and association operations to
gather data from the server and present either a table or tree view of
the relations that link a source instance and the target instances of an
association.
"""


from __future__ import absolute_import, print_function, unicode_literals

from collections import defaultdict, OrderedDict
import six
import click

# TODO: Future Could we combine this tree into tree file???
from asciitree import LeftAligned

from pywbem import CIMInstanceName, CIMClassName, \
    CIMFloat, CIMInt, CIMError, CIMDateTime
from pywbem._utils import _to_unicode, _ensure_unicode, _format

from ._common import output_format_is_table, format_table, shorten_path_str

# Same as in pwbem.cimtypes.py
if six.PY2:
    # pylint: disable=invalid-name,undefined-variable
    _Longint = long  # noqa: F821
else:
    # pylint: disable=invalid-name
    _Longint = int


class AssociationShrub(object):  # pylint: disable=useless-object-inheritance
    """
    This class provides tools for the acquisition and display of an association
    that includes much more information than the DMTF defined operation
    Associatiors.  Using the same input parameters, it allows displaying
    the the components that make up an association as either a table or a
    tree including the reference classes, and roles.
    """
    def __init__(self, context, source_path, Role=None, AssocClass=None,
                 ResultRole=None, ResultClass=None, fullpath=True,
                 verbose=None):
        self.source_path = source_path
        # list of all unique hosted_classnames for reference classes.
        # This is list of CIMClassName to insure that we provide host, namespace
        # where necessary
        # self.reference_classnames = []
        self.context = context
        self.conn = context.conn
        self.role = Role
        self.assoc_class = AssocClass
        self.result_role = ResultRole
        self.result_class = ResultClass
        self.verbose = verbose
        self.fullpath = fullpath

        #  Dictionary view of the shrub. This is a dictionary of dictionaries
        #  role:ReferenceClassNames:
        self.shrub_dict = OrderedDict()

        # associated instance names dictionary organized by:
        #   - reference_class,
        #   - role,
        #   - associated class
        # NOTE: To account for issues where there is an error getting data from
        # host, the concept of a "None" role exists.
        self.assoc_instnames = OrderedDict()

        self.source_namespace = source_path.namespace or \
            self.conn.default_namespace

        self.source_host = source_path.host or self.conn.host

        # Cache for the results of conn.ReferenceNames(self.source+path)
        self.reference_names = None

        # Copy of source_path with namespace
        self.full_source_path = self.source_path.copy()
        if self.full_source_path.namespace is None:
            self.full_source_path.namespace = self.source_namespace

        self.ternary_ref_classes = OrderedDict()

        self._build_shrub()

    @property
    def reference_classnames(self):
        """
        Return a list of the reference class names in the current shrub.
        This returns a list of objects of the class pywbem:CIMClassname
        which contains the name, host, and namespace for each class.
        """
        # pylint: disable=unnecessary-comprehension
        return [cln for cln in self.shrub_dict]

    def simplify_path(self, path):
        """
        Simplify the CIMamespace instance defined by path by copying and
        removing the host name and namespace name if they are the same as
        the source instance.  This allows the tree to show only the
        classname for all components of the tree that are in the same
        namespace as the association source instance.
        """
        display_path = path.copy()
        if display_path.host and \
                display_path.host.lower() == self.source_host.lower():
            display_path.host = None
        if display_path.namespace and \
                display_path.namespace.lower() == self.source_namespace.lower():
            display_path.namespace = None
        return display_path

    def _get_reference_roles(self, inst_name):
        """
        Internal method to get the list of roles for an association class.
        This uses the instance get rather than class get because some
        servers may not support class get operation.
        """
        try:
            ref_inst = self.conn.GetInstance(inst_name, LocalOnly=False)
        except CIMError as ce:
            click.echo('Exception ref {}, exception: {}'.format(inst_name, ce))
            return None
        roles = [pname for pname, pvalue in six.iteritems(ref_inst.properties)
                 if pvalue.type == 'reference']
        if self.verbose:
            print('class %s, roles %s' % (inst_name.classname, roles))
        return roles

    def _get_role_result_roles(self, roles, ref_classname):
        """
        Given the reference classname, separate the role and result_role
        parameters and return them. This method determines that the role
        is the call to ReferenceNames that returns references. Result roles
        are the roles that do not return references. Note that there are
        cases where this basic algorithm returns multiple
        """
        rtn_roles = {}
        for tst_role in roles:
            refs = self.conn.ReferenceNames(self.source_path,
                                            Role=tst_role,
                                            ResultClass=ref_classname)
            self.reference_names = refs
            # TODO where do we account for no references at all.
            # if refs returned, this is valid role that has at least one
            # reference
            if refs:
                rtn_roles[tst_role] = [r for r in roles if r != tst_role]
        if self.verbose:
            print('ResultRoles: class=%s ResultClass=%s ResultRoles=%s'
                  % (self.source_path.classname, ref_classname, rtn_roles))
        return rtn_roles

    def _build_shrub(self):
        """
        Build the internal representation of a tree for the shrub as a
        dictionary of dictionaries
        """
        # Build CIMClassname with host, namespace and insert if not
        # already in the class_roles dictionary. Get the instance from
        # the host and  roles from the instance.
        # ref_class_roles dictionary {<cln>:[roles]}
        ref_class_roles = {}
        ref_insts = self.conn.References(self.source_path)
        refnames = [i.path for i in ref_insts]

        # Build dictionary of reference classes in References return with
        # count of number of ref properties in each class
        for ref_inst in ref_insts:
            count = 0
            if ref_inst.classname not in self.ternary_ref_classes:
                for v in ref_inst.properties.values():
                    if v.type == 'reference':
                        count += 1
                assert count >= 2
                self.ternary_ref_classes[ref_inst.classname] = count > 2

        for ref in refnames:
            cln = CIMClassName(ref.classname, ref.host, ref.namespace)
            if cln not in ref_class_roles:
                ref_class_roles[cln] = self._get_reference_roles(ref)

        # find the role parameter and insert into shrub_dict.
        # The result is dictionary of form:
        #   {<role>:{<ASSOC_CLASS>:[RESULTROLES]}
        for cln, roles in six.iteritems(ref_class_roles):
            role_dict = self._get_role_result_roles(roles, cln.classname)

            # insert the role and cln into the shrub_dict
            for role, result_roles in role_dict.items():
                if role not in self.shrub_dict:
                    self.shrub_dict[role] = OrderedDict()
                    # TODO: This should be local, not in the shrub_dict
                    # Next code block cvts it to defaultdict
                    if cln not in self.shrub_dict[role]:
                        self.shrub_dict[role][cln] = result_roles

        # Find associated instances/classes
        for role in self.shrub_dict:
            self.assoc_instnames[role] = OrderedDict()
            for ref_classname in self.shrub_dict[role]:
                # Create associator result dictionaries with ref_class as key
                self.assoc_instnames[role][ref_classname] = OrderedDict()
                # TODO HERE IS ONE PLACE WE USE THE TEMP list in
                # shrub_dict [role][cln]: result_roles. REMOVE THIS
                result_roles = self.shrub_dict[role][ref_classname]
                self.shrub_dict[role][ref_classname] = defaultdict(list)

                # get the Associated class names by AssocClass and ResultRole
                assoc_clns = []
                for result_role in result_roles:
                    # Get the associated instance names from server for
                    # all result_classes
                    rtnd_assoc_names = self.conn.AssociatorNames(
                        self.source_path,
                        Role=role,
                        AssocClass=ref_classname,
                        ResultRole=result_role)

                    # Build unique associated classnames from returned
                    # AssociatorNames with a set comprehension
                    rtnd_clns = {
                        CIMClassName(iname.classname,
                                     iname.host,
                                     iname.namespace)
                        for iname in rtnd_assoc_names}

                    assoc_clns.extend(rtnd_clns)
                    self.shrub_dict[role][ref_classname][result_role]. \
                        extend(rtnd_clns)

                    # Get the associated instance names by AssocClass, role and
                    # target name using the aclassnames from above

                    disp_result_role = result_role or "None"
                    # Get AssociatorNames for specific ResultClass
                    for assoc_cln in assoc_clns:
                        anames = self.conn.AssociatorNames(
                            self.source_path,
                            Role=role,
                            AssocClass=ref_classname,
                            ResultRole=result_role,
                            ResultClass=assoc_cln)

                        # Build tuple of name, ref_inst  integer
                        # This ties each output instance to a particular
                        # reference instance.
                        aname_tuples = []
                        for aname in anames:
                            for ref_inst_ctr, ref_inst in enumerate(ref_insts):
                                if role not in ref_inst:
                                    continue
                                if ref_inst.get(role) != self.full_source_path:
                                    continue
                                # find other properties with this result_role
                                # and create a tuple for each one found
                                # The second data in the tuple identifies the
                                # reference instance by its position in the
                                # list of reference instances.
                                for name in ref_inst.properties:
                                    if name.lower() == result_role.lower():
                                        pvalue = ref_inst.properties[name].value
                                        anamex = aname.copy()
                                        anamex.host = None
                                        if pvalue == anamex:
                                            aname_tuples.append((aname,
                                                                 ref_inst_ctr))
                        # pylint: disable=line-too-long
                        if disp_result_role not in self.assoc_instnames[role][ref_classname]:  # noqa: E501
                            self.assoc_instnames[role][ref_classname][disp_result_role] = OrderedDict()  # noqa: E501

                        self.assoc_instnames[role][ref_classname][disp_result_role][assoc_cln] = aname_tuples  # noqa: E501

    def display_shrub(self, output_format, summary=None):
        """
        Build the shrub output and display it to the output device based on
        the output_format.
        The default ouput format is ascii tree
        """

        if output_format_is_table(output_format):
            click.echo(self.build_shrub_table(output_format, summary))

        # default is display as ascii tree
        else:
            click.echo(self.build_ascii_display_tree(summary))

    def build_ascii_display_tree(self, summary):
        """
        Build ascii tree display for current shrub.
        Returns an String with the formatted ASCII tree
        """
        tree = self.build_tree(summary)

        tr = LeftAligned()
        return tr(tree)

    def display_dicts(self, loc=None):
        """
        Development diagnostic to display dictionaries build by this class
        """
        # TODO: Remove this before release
        import pprint  # pylint: disable=import-outside-toplevel
        pp = pprint.PrettyPrinter(indent=4)
        if loc is None:
            loc = ""
        print('SHRUB_DICT %s' % loc)
        pp.pprint(self.shrub_dict)
        print('ASSOC_INST_NAMES %s' % loc)
        pp.pprint(self.assoc_instnames)

    def to_wbem_uri_folded(self, path, format='standard', max_len=15):
        # pylint: disable=redefined-builtin
        """
        Return the (untyped) WBEM URI string of this CIM instance path.
        This method modifies the pywbem:CIMInstanceName.to_wbem_uri method
        to return a slightly formated string where components are on
        separate lines if the length is longer than the max_len argument.

        See pywbem.CIMInstanceName.to_wbem_uri for detailed information

        Returns:

          :term:`unicode string`: Untyped WBEM URI of the CIM instance path,
          in the specified format.

        Raises:

          TypeError: Invalid type in keybindings
          ValueError: Invalid format
        """
        path = self.simplify_path(path)
        path_str = "{}".format(path)
        if len(path_str) <= max_len:
            return path_str

        ret = []

        def case(str_):
            """Return the string in the correct lexical case for the format."""
            if format == 'canonical':
                str_ = str_.lower()
            return str_

        def case_sorted(keys):
            """Return the keys in the correct order for the format."""
            if format == 'canonical':
                case_keys = [case(k) for k in keys]
                keys = sorted(case_keys)
            return keys

        if format not in ('standard', 'canonical', 'cimobject', 'historical'):
            raise ValueError(
                _format("Invalid format argument: {0}", format))

        if path.host is not None and format != 'cimobject':
            # The CIMObject format assumes there is no host component
            ret.append('//')
            ret.append(case(path.host))

        if path.host is not None or format not in ('cimobject', 'historical'):
            ret.append('/')

        if path.namespace is not None:
            ret.append(case(path.namespace))

        if path.namespace is not None or format != 'historical':
            ret.append(':')

        ret.append(case(path.classname))

        ret.append('.\n')

        for key in case_sorted(path.keybindings.iterkeys()):
            value = path.keybindings[key]

            ret.append(key)
            ret.append('=')

            if isinstance(value, six.binary_type):
                value = _to_unicode(value)

            if isinstance(value, six.text_type):
                # string, char16
                ret.append('"')
                ret.append(value.
                           replace('\\', '\\\\').
                           replace('"', '\\"'))
                ret.append('"')
            elif isinstance(value, bool):
                # boolean
                # Note that in Python a bool is an int, so test for bool first
                ret.append(str(value).upper())
            elif isinstance(value, (CIMFloat, float)):
                # realNN
                # Since Python 2.7 and Python 3.1, repr() prints float numbers
                # with the shortest representation that does not change its
                # value. When needed, it shows up to 17 significant digits,
                # which is the precision needed to round-trip double precision
                # IEE-754 floating point numbers between decimal and binary
                # without loss.
                ret.append(repr(value))
            elif isinstance(value, (CIMInt, int, _Longint)):
                # intNN
                ret.append(str(value))
            elif isinstance(value, CIMInstanceName):
                # reference
                ret.append('"')
                ret.append(value.to_wbem_uri(format=format).
                           replace('\\', '\\\\').
                           replace('"', '\\"'))
                ret.append('"')
            elif isinstance(value, CIMDateTime):
                # datetime
                ret.append('"')
                ret.append(str(value))
                ret.append('"')
            else:
                raise TypeError(
                    _format("Invalid type {0} in keybinding value: {1!A}={2!A}",
                            type(value), key, value))
            ret.append(',\n')

        del ret[-1]

        return _ensure_unicode(''.join(ret))

    def build_inst_names(self, inst_names_tuple, ref_cln, replacements,
                         fullpath=None):
        """
        Build a set of displayable instance names from the inst_names. This
        method tries to simplify the instance names by

        1. Hiding keys that have the same value for all instances. This
           is ignored if there is only a single instance
        2. Hiding certain specific key names that have a common meaning
        throughout the environment including SystemName,
        SystemCreationClassName, and CreationClassName.
        It hides CreationClassName key if the value is the same as the key
        classname.

        Next, if the defining reference class has more than 2 reference
        properties (ternary or greater associations) add an element to the
        instance name display indicate which reference instance is the
        connection for this association instance.

        Finally it removes the host and namespace if they are the same as
        the current host and namespace

        Parameters:

          inst_names_tuple
            tuple containing instancename and TODO

          ref_cln (:term:`string`):
             Classname of the reference class.

          replacements (TODO)

          fullpath (boolean):
            If True, show the full path.  If not True, build the path
            shortened by modifyin selected keys.
        """
        assert isinstance(inst_names_tuple, list)
        assert isinstance(inst_names_tuple[0], tuple)
        assert len(inst_names_tuple[0]) == 2
        assert isinstance(replacements, dict)

        # If path shortening specified, determine which keys can be shortend
        # based on keys with the same value in all instance names
        if not fullpath:
            first_iname = inst_names_tuple[0][0]
            keys_to_hide = {k: True for k in first_iname.keys()}

            # Determine if there are multiple instances with same value
            if len(inst_names_tuple) > 1:
                for iname_tuple in inst_names_tuple:
                    iname = iname_tuple[0]
                    for kbname, kbvalue in iname.items():
                        if kbname not in replacements:
                            if kbvalue != first_iname.keybindings[kbname]:
                                keys_to_hide[kbname] = False
                replacements = {k: None for k, v in keys_to_hide.items() if v}

            # Test for CreationClassName. Hide if same as classname
            ccn = "CreationClassName".lower()
            for iname_tuple in inst_names_tuple:
                iname = iname_tuple[0]
                for kbname, kbvalue in iname.keybindings.items():
                    if kbname.lower() == ccn:
                        if iname.keybindings[ccn] == iname.classname.lower():
                            replacements["CreationClassName"] = None

        ternary = True if self.ternary_ref_classes[ref_cln.classname] else False

        modified_inames = {}
        for inst_name in inst_names_tuple:
            iname = self.simplify_path(inst_name[0])
            # Shorten the path components if fullpath is set False
            if not self.fullpath:
                iname_display = shorten_path_str(iname, replacements)
            else:
                # This string conversion should match the one in shorten_...
                iname_display = iname.to_wbem_uri()

            # If reference class with more than 2 references add indicator
            # to the defining reference instance so the user can mathc
            # the instances to reference instances.
            if ternary:
                iname_display = '{}(refinst:{})'.format(iname_display,
                                                        inst_name[1])

            # builds dict with empty value to be ascii_tree compatible
            modified_inames[iname_display] = {}
        return modified_inames

    def build_tree(self, summary):
        """
        Prepare an ascii tree form of the shrub showing the hiearchy of
        components of the shrub. The top is the association source instance.
        The levels of the tree are:
            source instance
                role
                    reference_classe
                        result_role
                            result_classe
                                result_instances
        """
        assoctree = OrderedDict()
        for role, ref_clns in six.iteritems(self.shrub_dict):
            elementstree = OrderedDict()
            for ref_cln in ref_clns:
                rrole_dict = {}
                for rrole, assoc_clns in six.iteritems(
                        self.assoc_instnames[role][ref_cln]):
                    assoc_clns_dict = {}

                    for assoc_cln, inst_names in six.iteritems(assoc_clns):
                        disp_assoc_cln = self.simplify_path(assoc_cln)
                        key = "{}(ResultClass)({} insts)". \
                            format(disp_assoc_cln, len(inst_names))
                        if len(inst_names) != 0:
                            # build dictionary of associated instance names
                            assoc_clns_dict[key] = {}
                            if not summary:
                                # Create dictionary of standard keys to
                                # potentially hide. For now we always hide
                                # the following independent of key value
                                replacements = {
                                    "SystemCreationClassName": None,
                                    "SystemName": None}
                                # insts dict is keys only with empty sub-dict
                                # for ascii tree compatibility. i.e. this
                                # is the lowest level in the tree.
                                inst_names = self.build_inst_names(
                                    inst_names,
                                    ref_cln,
                                    replacements,
                                    self.fullpath)
                                assoc_clns_dict[key] = inst_names

                    # add the role tree element
                    rrole_disp = "{}(ResultRole)".format(rrole)
                    rrole_dict[rrole_disp] = assoc_clns_dict

                # Add the reference class element. Include namespace if
                # different than conn default namespace
                disp_ref_cln = "{}(AssocClass)". \
                    format(self.simplify_path(ref_cln))

                elementstree[disp_ref_cln] = rrole_dict

            # Add the role component to the tree
            disp_role = "{}(Role)".format(role)
            assoctree[disp_role] = elementstree

        # Attach the top of the tree, the source instance path for the
        # shrub.
        display_source_path = self.simplify_path(self.source_path)
        toptree = {display_source_path: assoctree}

        return toptree

    def build_shrub_table(self, output_format, summary):
        """
        Build and return a table representing the shrub. The table
        returned is a string that can be printed to a terminal or or other
        destination.
        """
        def fmt_inst_col(iname_tuples, max_len, summary, ternary):
            """
            Format the instance column display either as a summary count
            or a list of instances possibly with attached integer representing
            reference instance and return it as a single string
            """
            if summary:
                return len(iname_tuples)

            if ternary:
                return "\n".join("{}(refinst:{})".format(
                    self.to_wbem_uri_folded(t[0], max_len=max_len), t[1])
                                 for t in iname_tuples)  # noqa E128
            else:
                return "\n".join("{}".format(
                    self.to_wbem_uri_folded(t[0], max_len=max_len))
                                 for t in iname_tuples)  # noqa E128

        # Display shrub as table
        inst_hdr = "Assoc Inst Count" if summary else "Assoc Inst paths"
        headers = ["Role", "AssocClass", "ResultRole", "ResultClass", inst_hdr]
        rows = []
        # assoc_classnames [role]:[ref_clns]:[rrole]:[assoc_clns]
        for role, ref_clns in six.iteritems(self.shrub_dict):
            for ref_cln in ref_clns:
                ref_clns = self.shrub_dict[role][ref_cln]
                is_ternary = self.ternary_ref_classes[ref_cln.classname]
                for rrole, assoc_clns in six.iteritems(ref_clns):
                    for assoc_cln in assoc_clns:
                        inst_names = self.assoc_instnames[role][ref_cln][rrole][assoc_cln]  # noqa E501
                        ml = click.get_terminal_size()[0] - 65
                        # TODO ks: Create more general width algorithm

                        inst_col = fmt_inst_col(inst_names, ml, summary,
                                                is_ternary)

                        rows.append([role,
                                     self.simplify_path(ref_cln),
                                     rrole,
                                     self.simplify_path(assoc_cln),
                                     inst_col])

        title = 'Shrub of {}'.format(self.source_path)
        return format_table(rows, headers, title, table_format=output_format)
