import React from 'react';
import { commonArgTypes, commonParameters } from '../stories-helpers';
import Button from './index';

export default {
  title: '../Button',
  component: Button,
  argTypes: {
    ...commonArgTypes,
    variant: {
      control: {
        type: 'select',
        options: ['contained', 'outlined', 'default'],
      }
    },
    size: {
      control: {
        type: 'select',
        options: ['small', 'medium', 'large'],
      }
    },
    disabled: {
      control: {
        type: 'boolean',
      }
    },
  },
  parameters: commonParameters,
};

const Template = (args) => <Button {...args}>Button</Button>;

export const Primary = Template.bind({});

Primary.args = {
  variant: 'contained',
  color: 'primary',
};

export const Outlined = Template.bind({});

Outlined.args = {
  variant: 'outlined',
  color: 'secondary',
};

const SizeSamples = (args) => (
  <>
    <Button size="small" {...args}>Small</Button> &nbsp;
    <Button size="medium" {...args}>Medium</Button> &nbsp;
    <Button size="large" {...args}>Large</Button>
  </>
);

export const Sizes = SizeSamples.bind({});

Sizes.args = {
  variant: 'contained',
  color: 'primary',
};


const VariantSamples = (args) => (
  <>
    <Button variant="contained" {...args}>Contained</Button> &nbsp;
    <Button variant="outlined" {...args}>Outlined</Button> &nbsp;
    <Button {...args}>Text</Button>
  </>
);

export const Disabled = VariantSamples.bind({});

Disabled.args = {
  color: 'primary',
  disabled: true,
};
