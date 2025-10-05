'use client';

import { useState } from 'react';
import { SpecEditor } from '@/components/SpecEditor';
import { CodeViewer } from '@/components/CodeViewer';
import { ProofReport } from '@/components/ProofReport';
import { IterationHistory } from '@/components/IterationHistory';
import type { VerificationResult } from '@/lib/types/verification';
import { Button } from '@/components/ui/button';
import { Textarea } from '@/components/ui/textarea';
import { Spinner } from '@/components/ui/spinner';
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs"
import { Card, CardHeader, CardTitle, CardDescription, CardContent } from '@/components/ui/card';
import { Alert, AlertTitle, AlertDescription } from '@/components/ui/alert';
import { AlertCircle, CheckCircle2, XCircle, FileText, Zap } from 'lucide-react';
import type { ExamplesResponse } from '@/lib/types/api';
import { useVerificationStream } from '@/lib/hooks/useVerificationStream';
import { ProgressDisplay } from '@/components/ProgressDisplay';

export default function VerifyPage() {
  const [spec, setSpec] = useState('');
  const [result, setResult] = useState<VerificationResult | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [naturalLanguage, setNaturalLanguage] = useState('');
  const [generatedYaml, setGeneratedYaml] = useState('');
  const [isLoadingYaml, setIsLoadingYaml] = useState(false);
  const [yamlError, setYamlError] = useState<string | null>(null);
  const [progress, setProgress] = useState<string>('');
  const [useRealTime, setUseRealTime] = useState(true);

  // SSE hook for real-time updates
  const { streamState, startVerification, stopVerification } = useVerificationStream();

  const handleGenerate = async () => {
    setIsLoadingYaml(true);
    setYamlError(null);
    try {
      const response = await fetch('/api/generate-spec', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ naturalLanguage }),
      });
      const data = await response.json();
      if (data.yaml) {
        setGeneratedYaml(data.yaml);
      } else {
        setYamlError(data.error || 'Failed to generate YAML specification');
      }
    } catch (error) {
      setYamlError(error instanceof Error ? error.message : 'Failed to generate YAML specification');
    } finally {
      setIsLoadingYaml(false);
    }
  };

  const handleVerify = async () => {
    if (useRealTime) {
      // Use SSE for real-time updates
      await startVerification({
        spec: generatedYaml || spec,
        maxIterations: 8,
      });

      // Result will be available in streamState.result
      // This is handled by the hook automatically
    } else {
      // Legacy mode: single request/response
      setLoading(true);
      setError(null);
      setResult(null);
      setProgress('Parsing specification...');

      try {
        // Simulate progress steps (in real implementation, this would be from server-sent events)
        setTimeout(() => setProgress('Generating TypeScript code...'), 500);
        setTimeout(() => setProgress('Translating to TLA+ formal model...'), 1500);
        setTimeout(() => setProgress('Running TLC model checker...'), 3000);

        const response = await fetch('/api/verify', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ spec: generatedYaml || spec }),
        });

        const data = await response.json();
        if (data.success) {
          setProgress('Verification complete!');
          setResult(data.result);
        } else {
          setError(data.error || 'Verification failed');
        }
      } catch (error) {
        setError(error instanceof Error ? error.message : 'Verification failed - please check your specification');
      } finally {
        setLoading(false);
        setProgress('');
      }
    }
  };

  const handleCodeGenOnly = async () => {
    setLoading(true);
    setError(null);
    setResult(null);
    setProgress('Generating TypeScript code...');

    try {
      const response = await fetch('/api/generate-code', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ spec: generatedYaml || spec }),
      });

      const data = await response.json();
      if (data.success && data.code) {
        // Create a minimal result for display
        setResult({
          success: true,
          iterations: 1,
          finalCode: data.code,
        });
      } else {
        setError(data.error || 'Code generation failed');
      }
    } catch (error) {
      setError(error instanceof Error ? error.message : 'Code generation failed');
    } finally {
      setLoading(false);
      setProgress('');
    }
  };

  const loadExample = async (exampleName: 'transfer' | 'write') => {
    try {
      const response = await fetch('/api/examples');
      const data: ExamplesResponse = await response.json();

      const example = data.examples.find(ex =>
        exampleName === 'transfer' ? ex.category === 'transfer' : ex.category === 'write'
      );

      if (example) {
        setGeneratedYaml(example.yaml);
        setSpec(example.yaml);
      }
    } catch (error) {
      setError('Failed to load example');
    }
  };

  return (
    <Tabs defaultValue="generate" className="w-full">
      <TabsList className="grid w-full grid-cols-2">
        <TabsTrigger value="generate">1. Generate Specification</TabsTrigger>
        <TabsTrigger value="verify">2. Verify Implementation</TabsTrigger>
      </TabsList>
      <TabsContent value="generate">
        <Card>
          <CardHeader>
            <CardTitle>Generate Specification from Natural Language</CardTitle>
            <CardDescription>Describe the desired behavior in plain English, and we'll generate the YAML specification for you.</CardDescription>
          </CardHeader>
          <CardContent className="space-y-4">
            <Textarea
              placeholder="e.g., A function that transfers money between two accounts, ensuring that the money is not lost or duplicated..."
              value={naturalLanguage}
              onChange={(e) => setNaturalLanguage(e.target.value)}
              rows={10}
            />
            <Button onClick={handleGenerate} disabled={isLoadingYaml} className="w-full">
              {isLoadingYaml ? <Spinner size="sm" /> : 'Generate YAML'}
            </Button>
            {yamlError && (
              <Alert variant="destructive">
                <AlertCircle className="h-4 w-4" />
                <AlertTitle>Generation Failed</AlertTitle>
                <AlertDescription>{yamlError}</AlertDescription>
              </Alert>
            )}
            <Textarea
              placeholder="Generated YAML will appear here..."
              value={generatedYaml}
              onChange={(e) => setGeneratedYaml(e.target.value)}
              rows={20}
              className="font-mono text-sm bg-gray-50 focus:bg-white transition-colors duration-200"
            />
          </CardContent>
        </Card>
      </TabsContent>
      <TabsContent value="verify">
        <Card>
          <CardHeader>
            <CardTitle>Verify Implementation</CardTitle>
            <CardDescription>Provide a YAML specification to generate and verify a formally correct implementation.</CardDescription>
          </CardHeader>
          <CardContent className="space-y-4">
            <div className="flex gap-2 mb-4">
              <Button onClick={() => loadExample('transfer')} variant="outline" size="sm">
                <FileText className="h-4 w-4 mr-2" />
                Load Transfer Example
              </Button>
              <Button onClick={() => loadExample('write')} variant="outline" size="sm">
                <FileText className="h-4 w-4 mr-2" />
                Load Write Example
              </Button>
            </div>

            {/* Real-time toggle */}
            <div className="flex items-center gap-2 p-3 bg-blue-50 rounded-lg border border-blue-200">
              <input
                type="checkbox"
                id="realtime"
                checked={useRealTime}
                onChange={(e) => setUseRealTime(e.target.checked)}
                className="w-4 h-4"
              />
              <label htmlFor="realtime" className="flex items-center gap-2 text-sm font-medium text-blue-900 cursor-pointer">
                <Zap className="h-4 w-4" />
                Enable Real-Time Progress Updates (SSE)
              </label>
            </div>

            <SpecEditor onChange={setSpec} initialValue={generatedYaml} />
            <div className="flex gap-2">
              <Button
                onClick={handleVerify}
                disabled={(useRealTime ? streamState.isStreaming : loading) || (!spec && !generatedYaml)}
                className="flex-1"
              >
                {(useRealTime ? streamState.isStreaming : loading) ? (
                  <div className="flex items-center gap-2">
                    <Spinner size="sm" />
                    <span className="text-sm">{useRealTime ? streamState.currentPhase : progress}</span>
                  </div>
                ) : 'Run Full Verification'}
              </Button>
              <Button onClick={handleCodeGenOnly} disabled={loading || (!spec && !generatedYaml)} variant="outline" className="flex-1">
                {loading ? <Spinner size="xs" /> : 'Generate Code Only'}
              </Button>
            </div>
          </CardContent>
        </Card>

        {/* Real-time Progress Display */}
        {useRealTime && (streamState.isStreaming || streamState.events.length > 0) && (
          <ProgressDisplay streamState={streamState} />
        )}

        {/* Error Display */}
        {(error || streamState.error) && (
          <Alert variant="destructive" className="mt-4">
            <XCircle className="h-4 w-4" />
            <AlertTitle>Verification Failed</AlertTitle>
            <AlertDescription>{error || streamState.error}</AlertDescription>
          </Alert>
        )}

        {/* Success Display */}
        {((result && result.success) || (streamState.result && streamState.result.success)) && (
          <Alert className="mt-4 border-green-200 bg-green-50 text-green-800">
            <CheckCircle2 className="h-4 w-4 text-green-600" />
            <AlertTitle>Verification Successful!</AlertTitle>
            <AlertDescription>
              Code verified in {(result || streamState.result)!.iterations} iteration{(result || streamState.result)!.iterations !== 1 ? 's' : ''}.
              {(result || streamState.result)!.proofReport && ` Explored ${(result || streamState.result)!.proofReport!.statesExplored.toLocaleString()} states.`}
            </AlertDescription>
          </Alert>
        )}

        {/* Results Display */}
        {(result || streamState.result) && (
          <div className="space-y-8 mt-8">
            {(result || streamState.result)!.finalCode && (
              <CodeViewer code={(result || streamState.result)!.finalCode!} />
            )}

            {(result || streamState.result)!.iterationHistory && (
              <IterationHistory iterations={(result || streamState.result)!.iterationHistory!} />
            )}

            {(result || streamState.result)!.proofReport && (
              <ProofReport report={(result || streamState.result)!.proofReport!} />
            )}
          </div>
        )}
      </TabsContent>
    </Tabs>
  );
}
