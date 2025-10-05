'use client';

import { useState } from 'react';
import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Button } from '@/components/ui/button';
import { Badge } from '@/components/ui/badge';
import { Copy, Download } from 'lucide-react';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { vscDarkPlus } from 'react-syntax-highlighter/dist/esm/styles/prism';

interface CodeViewerProps {
  code: string;
  language?: 'typescript' | 'tlaplus';
  title?: string;
}

export function CodeViewer({
  code,
  language = 'typescript',
  title = 'Generated Code'
}: CodeViewerProps) {
  const [copied, setCopied] = useState(false);

  const handleCopy = () => {
    navigator.clipboard.writeText(code);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };

  const handleDownload = () => {
    const extension = language === 'tlaplus' ? 'tla' : 'ts';
    const blob = new Blob([code], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `generated-code.${extension}`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  return (
    <Card className="shadow-lg bg-white">
      <CardHeader className="flex flex-row items-center justify-between">
        <CardTitle>{title}</CardTitle>
        <div className="flex items-center gap-2">
          <Badge variant="secondary">{language}</Badge>
          <Button variant="ghost" size="icon" onClick={handleCopy} title={copied ? 'Copied!' : 'Copy code'}>
            <Copy className={`h-4 w-4 ${copied ? 'text-green-600' : ''}`} />
          </Button>
          <Button variant="ghost" size="icon" onClick={handleDownload} title="Download code">
            <Download className="h-4 w-4" />
          </Button>
        </div>
      </CardHeader>
      <CardContent className="bg-gray-900 text-gray-100 rounded-b-lg p-0">
        <SyntaxHighlighter
          language={language === 'tlaplus' ? 'text' : 'typescript'}
          style={vscDarkPlus}
          customStyle={{
            margin: 0,
            borderRadius: '0 0 0.5rem 0.5rem',
            fontSize: '0.875rem',
          }}
          showLineNumbers
        >
          {code}
        </SyntaxHighlighter>
      </CardContent>
    </Card>
  );
}
