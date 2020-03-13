#!/usr/bin/env python3

import hjson
import collections
import argparse
import sys
import os

DEFAULT_CONFIG_FILE = 'ibex_configs.hjson'

class ConfigException(Exception):
    pass

def verify_config(name, config_dict):
    """Check config_dict matches expectations:
        - It's a mapping object e.g. OrderedDict
        - It's values are either strings or integers"""
    if not isinstance(config_dict, collections.Mapping):
        raise ConfigException('Config ' + name + ' must have dictionary giving parameters')

    for k, v in config_dict.items():
        if isinstance(v, int):
            continue
        if isinstance(v, str):
            continue

        raise ConfigException('Parameter ' + k + ' for config ' + name +
            ' must be string or int got ' + str(type(v)))

def get_config_dicts(config_file):
    """From a open file config_file extract a dictionary of configuration
    dictionaries

    Throws ConfigException on any error"""
    try:
        config_hjson = hjson.load(config_file)

        for k, v in config_hjson.items():
            verify_config(k, v)

        verify_config_parameters(config_hjson)

        return config_hjson
    except hjson.HjsonDecodeError as e:
        raise ConfigException('Could not decode hjson ' + str(e))


def verify_config_parameters(config_dicts):
    """Verify parameters across config_dicts match expectations:
        - Each config has the same set of parameters specified"""
    parameters = set()

    first = True

    for name, config_dict in config_dicts.items():
        parameters_this_config = set()

        for parameter, value in config_dict.items():
            if first:
                parameters.add(parameter)

            parameters_this_config.add(parameter)

        if first:
            first = False
        else:
            parameter_difference = parameters ^ parameters_this_config
            if len(parameter_difference) != 0:
                raise ConfigException('Config ' + name +
                    ' has differing parameters ' +
                    ','.join(parameter_difference))

def config_dict_to_fusesoc_opts(config_dict):
    fusesoc_cmd = []
    for parameter, value in config_dict.items():
        fusesoc_cmd.append('--' + parameter + '=' + str(value))

    return ' '.join(fusesoc_cmd)

def config_dict_to_csv(config_dct):
    pass

def get_config_file_location():
    """Returns the location of the config file, IBEX_CONFIG_FILE environment
    variable overrides the default"""

    if 'IBEX_CONFIG_FILE' in os.environ:
        return os.environ['IBEX_CONFIG_FILE']

    return DEFAULT_CONFIG_FILE

def main():
    config_outputs = {
        'fusesoc_opts' : config_dict_to_fusesoc_opts,
        'csv'          : config_dict_to_csv,
    }

    argparser = argparse.ArgumentParser(description="""Outputs Ibex configuration
    parameters for a named config in a number of formats""")

    argparser.add_argument('config_name', help="""The name of the Ibex
    configuration to output""")

    argparser.add_argument('output_type', help="""Format to output the
    configuration parameters in""", choices = config_outputs.keys())

    argparser.add_argument('--config_filename', help="""Config file to read""",
            default = get_config_file_location())

    args = argparser.parse_args()

    try:
        config_file = open(args.config_filename)
        config_dicts = get_config_dicts(config_file)

        if args.config_name not in config_dicts:
            print('ERROR: configuration', args.config_name, 'not found in',
                    args.config_filename, file=sys.stderr)

            sys.exit(1)

        print(config_outputs[args.output_type](config_dicts[args.config_name]))
    except ConfigException as ce:
        print('ERROR: failure to read configuration from', args.config_name, ce, file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
