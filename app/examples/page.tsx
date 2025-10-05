'use client';

import { useEffect, useState } from 'react';
import { ExampleSpec } from '@/lib/types/api';
import { SpecEditor } from '@/components/SpecEditor';
import { Card, CardHeader, CardTitle, CardDescription, CardContent } from '@/components/ui/card';

export default function ExamplesPage() {
  const [examples, setExamples] = useState<ExampleSpec[]>([]);
  const [selected, setSelected] = useState<ExampleSpec | null>(null);

  useEffect(() => {
    fetch('/api/examples')
      .then(res => res.json())
      .then(data => {
        setExamples(data.examples);
        if (data.examples.length > 0) {
          setSelected(data.examples[0]);
        }
      });
  }, []);

  return (
    <div className="grid grid-cols-1 md:grid-cols-3 gap-8">
      <div className="md:col-span-1">
        <Card className="shadow-lg">
          <CardHeader>
            <CardTitle>Examples</CardTitle>
            <CardDescription>Select an example to view its specification.</CardDescription>
          </CardHeader>
          <CardContent className="space-y-2">
            {examples.map((example) => (
              <div
                key={example.name}
                onClick={() => setSelected(example)}
                className={`p-4 rounded-lg cursor-pointer transition-all duration-200 ${
                  selected?.name === example.name
                    ? 'bg-gray-200 shadow-inner'
                    : 'hover:bg-gray-100 hover:shadow-md'
                }`}>
                <p className="font-semibold">{example.name}</p>
                <p className="text-sm text-gray-600 mt-1">{example.description}</p>
              </div>
            ))}
          </CardContent>
        </Card>
      </div>
      <div className="md:col-span-2">
        {selected && (
          <SpecEditor
            initialValue={selected.yaml}
            readOnly
          />
        )}
      </div>
    </div>
  );
}
