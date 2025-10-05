'use client';

import { useState, useEffect } from 'react';
import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Textarea } from '@/components/ui/textarea';

interface SpecEditorProps {
  initialValue?: string;
  onChange?: (value: string) => void;
  readOnly?: boolean;
}

export function SpecEditor({
  initialValue = '',
  onChange,
  readOnly = false
}: SpecEditorProps) {
  const [value, setValue] = useState(initialValue);

  useEffect(() => {
    setValue(initialValue);
  }, [initialValue]);

  const handleChange = (newValue: string) => {
    setValue(newValue);
    onChange?.(newValue);
  };

  return (
    <Card className="shadow-lg bg-white">
      <CardHeader>
        <CardTitle>Specification (YAML)</CardTitle>
      </CardHeader>
      <CardContent>
        <Textarea
          value={value}
          onChange={(e) => handleChange(e.target.value)}
          readOnly={readOnly}
          placeholder="Enter your YAML specification..."
          rows={20}
          className="font-mono text-sm bg-gray-50 focus:bg-white transition-colors duration-200"
        />
      </CardContent>
    </Card>
  );
}
